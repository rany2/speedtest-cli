#!/usr/bin/env python3

# Copyright 2012 Matt Martz
# All Rights Reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

import csv
import errno
import itertools
import json
import math
import signal
import ssl
import sys
import threading
import time
import timeit
import xml.etree.ElementTree as ET
from argparse import SUPPRESS as ARG_SUPPRESS
from argparse import ArgumentParser as ArgParser
from concurrent.futures import ThreadPoolExecutor
from copy import copy
from datetime import datetime, timezone
from hashlib import md5
from http.client import BadStatusLine, HTTPSConnection
from io import BytesIO, StringIO
from queue import Queue
from urllib.parse import parse_qs, urlencode
from urllib.request import (AbstractHTTPHandler, HTTPDefaultErrorHandler,
                            HTTPErrorProcessor, HTTPRedirectHandler,
                            OpenerDirector, ProxyHandler, Request)

try:
    import gzip

    GzipBase = gzip.GzipFile
except ImportError:
    gzip = None
    GzipBase = object

__version__ = "2.1.4b1"

# Some global variables we use
DEBUG = False

# Common exceptions to catch
HTTP_ERRORS = (
    BadStatusLine,
    OSError,
    ssl.CertificateError,
)


class SpeedtestException(Exception):
    """Base exception for this module"""


class SpeedtestCLIError(SpeedtestException):
    """Generic exception for raising errors during CLI operation"""


class SpeedtestHTTPError(SpeedtestException):
    """Base HTTP exception for this module"""


class SpeedtestConfigError(SpeedtestException):
    """Configuration XML is invalid"""


class SpeedtestServersError(SpeedtestException):
    """Servers JSON is invalid"""


class ConfigRetrievalError(SpeedtestHTTPError):
    """Could not retrieve config.php"""


class ServersRetrievalError(SpeedtestHTTPError):
    """Could not retrieve speedtest-servers.php"""


class InvalidServerIDType(SpeedtestException):
    """Server ID used for filtering was not an integer"""


class NoMatchedServers(SpeedtestException):
    """No servers matched when filtering"""


class ShareResultsConnectFailure(SpeedtestException):
    """Could not connect to speedtest.net API to POST results"""


class ShareResultsSubmitFailure(SpeedtestException):
    """Unable to successfully POST results to speedtest.net API after
    connection
    """


class SpeedtestUploadTimeout(SpeedtestException):
    """testlength configuration reached during upload
    Used to ensure the upload halts when no additional data should be sent
    """


class SpeedtestBestServerFailure(SpeedtestException):
    """Unable to determine best server"""


class SpeedtestHTTPSConnection(HTTPSConnection):
    """Custom HTTPSConnection to support source_address"""

    def __init__(self, *args, **kwargs):
        verify = kwargs.pop("verify", True)
        if not verify:
            ctx = ssl.create_default_context()
            ctx.verify_mode = ssl.CERT_NONE
            ctx.check_hostname = False
            kwargs["context"] = ctx

        super().__init__(*args, **kwargs)


def _build_connection(connection, **kwargs):
    """Called from ``https_open`` methods of ``SpeedtestHTTPSHandler``"""

    def inner(host, **kwargs_inner):
        kwargs.update(kwargs_inner)
        return connection(host, **kwargs)

    return inner


class SpeedtestHTTPSHandler(AbstractHTTPHandler):
    """Custom ``HTTPSHandler`` that can build a ``HTTPSConnection`` with the
    args we need for ``source_address`` and ``timeout``
    """

    def __init__(
        self, debuglevel=0, context=None, source_address=None, timeout=10, verify=True
    ):
        AbstractHTTPHandler.__init__(self, debuglevel)
        self._context = context
        self.source_address = source_address
        self.timeout = timeout
        self.verify = verify

    def https_open(self, req):
        return self.do_open(
            _build_connection(
                SpeedtestHTTPSConnection,
                source_address=self.source_address,
                timeout=self.timeout,
                verify=self.verify,
                context=self._context,
            ),
            req,
        )

    https_request = AbstractHTTPHandler.do_request_


def build_opener(source_address=None, timeout=10, verify=True):
    """Function similar to ``urllib2.build_opener`` that will build
    an ``OpenerDirector`` with the explicit handlers we want,
    ``source_address`` for binding, ``timeout`` and our custom
    `User-Agent`
    """

    printer(f"Timeout set to {int(timeout)}", debug=True)

    if source_address:
        source_address_tuple = (source_address, 0)
        printer(f"Binding to source address: {source_address_tuple!r}", debug=True)
    else:
        source_address_tuple = None

    handlers = [
        ProxyHandler(),
        SpeedtestHTTPSHandler(
            source_address=source_address_tuple, timeout=timeout, verify=verify
        ),
        HTTPDefaultErrorHandler(),
        HTTPRedirectHandler(),
        HTTPErrorProcessor(),
    ]

    opener = OpenerDirector()
    opener.addheaders = [("User-agent", build_user_agent())]

    for handler in handlers:
        opener.add_handler(handler)

    return opener


class GzipDecodedResponse(GzipBase):
    """A file-like object to decode a response encoded with the gzip
    method, as described in RFC 1952.

    Largely copied from ``xmlrpclib``/``xmlrpc.client`` and modified
    to work for py2.4-py3
    """

    def __init__(self, response):
        # response doesn't support tell() and read(), required by
        # GzipFile
        if not gzip:
            raise SpeedtestHTTPError(
                "HTTP response body is gzip encoded, "
                "but gzip support is not available"
            )
        self.io = BytesIO()
        while True:
            chunk = response.read(1024)
            if not chunk:
                break
            self.io.write(chunk)
        self.io.seek(0)
        gzip.GzipFile.__init__(self, mode="rb", fileobj=self.io)

    def close(self):
        try:
            gzip.GzipFile.close(self)
        finally:
            self.io.close()


def build_user_agent():
    """Build a Mozilla/5.0 compatible User-Agent string"""

    ua_tuple = (
        "Mozilla/5.0",
        "(KHTML, like Gecko)",
        f"speedtest-cli/{__version__}",
    )
    user_agent = " ".join(ua_tuple)
    printer(f"User-Agent: {user_agent}", debug=True)
    return user_agent


def build_request(url: str, data=None, headers=None):
    """Build a urllib2 request object

    This function automatically adds a User-Agent header to all requests
    """

    if not headers:
        headers = {}

    printer(f"{('GET', 'POST')[bool(data)]} {url}", debug=True)

    return Request(url, data=data, headers=headers)


def catch_request(request, *, opener: OpenerDirector):
    """Helper function to catch common exceptions encountered when
    establishing a connection with a HTTPS request
    """

    _open = opener.open
    try:
        uh = _open(request)
        if request.get_full_url() != uh.geturl():
            printer(f"Redirected to {uh.geturl()}", debug=True)
        return uh, False
    except HTTP_ERRORS as exc:
        return None, exc


def catch_thread_operation(
    *,
    shutdown_event: threading.Event,
    target,
    target_args=None,
    target_kwargs=None,
):
    """Helper function to catch common exceptions encountered when
    starting a thread
    """

    if target_args is None:
        target_args = ()
    if target_kwargs is None:
        target_kwargs = {}

    try:
        target(*target_args, **target_kwargs)
    except RuntimeError as exc:
        # if we are shutting down, don't raise exc
        # otherwise, raise exc... this is because when
        # we are shutting down, we cannot start any
        # new threads since Python 3.12+
        if not shutdown_event.is_set():
            raise exc


def get_response_stream(response):
    """Helper function to return either a Gzip reader if
    ``Content-Encoding`` is ``gzip`` otherwise the response itself
    """

    if response.getheader("content-encoding") == "gzip":
        return GzipDecodedResponse(response)

    return response


def print_dots(shutdown_event: threading.Event) -> callable:
    """Built in callback function used by Thread classes for printing
    status
    """

    def inner(current, total, end=False):
        if shutdown_event.is_set():
            return

        sys.stdout.write(".")
        if current + 1 == total and end is True:
            sys.stdout.write("\n")
        sys.stdout.flush()

    return inner


def repeat_elements(seq, n):
    """Repeat elements of a sequence n times"""
    return itertools.islice(itertools.cycle(seq), len(seq) * n)


def do_nothing(*_args, **_kwargs):
    pass


class HTTPDownloader(threading.Thread):
    """Thread class for retrieving a URL"""

    def __init__(self, i, request, start, timeout, *, opener, shutdown_event):
        threading.Thread.__init__(self)
        self.request = request
        self.result = [0]
        self.starttime = start
        self.timeout = timeout
        self.i = i
        self._opener = opener.open
        self._shutdown_event = shutdown_event

    def run(self):
        try:
            if (timeit.default_timer() - self.starttime) <= self.timeout:
                f = self._opener(self.request)
                while (
                    not self._shutdown_event.is_set()
                    and (timeit.default_timer() - self.starttime) <= self.timeout
                ):
                    self.result.append(len(f.read(10240)))
                    if self.result[-1] == 0:
                        break
                f.close()
        except OSError:
            pass
        except HTTP_ERRORS:
            pass


class HTTPUploaderData:
    """File like object to improve cutting off the upload once the timeout
    has been reached
    """

    def __init__(self, length, start, timeout, *, shutdown_event):
        self.length = length
        self.start = start
        self.timeout = timeout
        self._shutdown_event = shutdown_event

        self._data = None

        self.total = [0]

    def pre_allocate(self):
        chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        multiplier = int(round(int(self.length) / 36.0))
        try:
            self._data = BytesIO(
                (f"content1={(chars * multiplier)[0:int(self.length) - 9]}").encode()
            )
        except MemoryError as exc:
            raise SpeedtestCLIError(
                "Insufficient memory to pre-allocate upload data. Please "
                "use --no-pre-allocate"
            ) from exc

    @property
    def data(self):
        if not self._data:
            self.pre_allocate()
        return self._data

    def read(self, n=10240):
        if (
            timeit.default_timer() - self.start
        ) <= self.timeout and not self._shutdown_event.is_set():
            chunk = self.data.read(n)
            self.total.append(len(chunk))
            return chunk
        raise SpeedtestUploadTimeout()

    def __len__(self):
        return self.length


class HTTPUploader(threading.Thread):
    """Thread class for putting a URL"""

    def __init__(self, i, request, start, size, timeout, *, opener, shutdown_event):
        threading.Thread.__init__(self)
        self.request = request
        self.request.data.start = self.starttime = start
        self.size = size
        self.result = 0
        self.timeout = timeout
        self.i = i

        self._opener = opener.open
        self._shutdown_event = shutdown_event

    def run(self):
        request = self.request
        try:
            if (
                timeit.default_timer() - self.starttime
            ) <= self.timeout and not self._shutdown_event.is_set():
                with self._opener(request) as f:
                    f.read(11)
                self.result = sum(self.request.data.total)
            else:
                self.result = 0
        except (OSError, SpeedtestUploadTimeout):
            self.result = sum(self.request.data.total)
        except HTTP_ERRORS:
            self.result = 0


class SpeedtestResults:
    """Class for holding the results of a speedtest, including:

    Download speed
    Upload speed
    Ping/Latency to test server
    Data about server that the test was run against

    Additionally this class can return a result data as a dictionary or CSV,
    as well as submit a POST of the result data to the speedtest.net API
    to get a share results image link.
    """

    def __init__(
        self,
        download=0,
        upload=0,
        ping=0,
        server=None,
        client=None,
        opener=None,
    ):
        self.download = download
        self.upload = upload
        self.ping = ping
        if server is None:
            self.server = {}
        else:
            self.server = server
        self.client = client or {}

        self._share = None
        self.timestamp = f"{datetime.now(timezone.utc).isoformat()}Z"
        self.bytes_received = 0
        self.bytes_sent = 0

        self._opener = opener

    def __repr__(self):
        return repr(self.dict())

    def share(self):
        """POST data to the speedtest.net API to obtain a share results
        link
        """

        if self._share:
            return self._share

        download = int(round(self.download / 1000.0, 0))
        ping = int(round(self.ping, 0))
        upload = int(round(self.upload / 1000.0, 0))

        # Build the request to send results back to speedtest.net
        # We use a list instead of a dict because the API expects parameters
        # in a certain order
        api_data = [
            f"recommendedserverid={self.server['id']}",
            f"ping={ping}",
            "screenresolution=",
            "promo=",
            f"download={download}",
            "screendpi=",
            f"upload={upload}",
            "testmethod=http",
            f"hash={md5(f'{ping}-{upload}-{download}-297aae72'.encode()).hexdigest()}",
            "touchscreen=none",
            "startmode=pingselect",
            "accuracy=1",
            f"bytesreceived={self.bytes_received}",
            f"bytessent={self.bytes_sent}",
            f"serverid={self.server['id']}",
        ]

        headers = {"Referer": "http://c.speedtest.net/flash/speedtest.swf"}
        request = build_request(
            "https://www.speedtest.net/api/api.php",
            data="&".join(api_data).encode(),
            headers=headers,
        )

        try:
            f, e = catch_request(request, opener=self._opener)
            if e:
                raise ShareResultsConnectFailure(e)

            response = f.read()
            code = f.code
        finally:
            f.close()

        if int(code) != 200:
            raise ShareResultsSubmitFailure("Could not submit results to speedtest.net")

        qsargs = parse_qs(response.decode())
        resultid = qsargs.get("resultid")
        if not resultid or len(resultid) != 1:
            raise ShareResultsSubmitFailure("Could not submit results to speedtest.net")

        self._share = f"https://www.speedtest.net/result/{resultid[0]}.png"

        return self._share

    def dict(self):
        """Return dictionary of result data"""

        return {
            "download": self.download,
            "upload": self.upload,
            "ping": self.ping,
            "server": self.server,
            "timestamp": self.timestamp,
            "bytes_sent": self.bytes_sent,
            "bytes_received": self.bytes_received,
            "share": self._share,
            "client": self.client,
        }

    @staticmethod
    def csv_header(delimiter=","):
        """Return CSV Headers"""

        row = [
            "Server ID",
            "Sponsor",
            "Server Name",
            "Timestamp",
            "Distance",
            "Ping",
            "Download",
            "Upload",
            "Share",
            "IP Address",
        ]
        out = StringIO()
        writer = csv.writer(out, delimiter=delimiter, lineterminator="")
        writer.writerow(row)
        return out.getvalue()

    def csv(self, delimiter=","):
        """Return data in CSV format"""

        data = self.dict()
        out = StringIO()
        writer = csv.writer(out, delimiter=delimiter, lineterminator="")
        row = [
            data["server"]["id"],
            data["server"]["sponsor"],
            data["server"]["name"],
            data["timestamp"],
            data["server"]["d"],
            data["ping"],
            data["download"],
            data["upload"],
            self._share or "",
            self.client["ip"],
        ]
        writer.writerow(row)
        return out.getvalue()

    def json(self, pretty=False):
        """Return data in JSON format"""

        kwargs = {}
        if pretty:
            kwargs.update({"indent": 4, "sort_keys": True})
        return json.dumps(self.dict(), **kwargs)


class Speedtest:
    """Class for performing standard speedtest.net testing operations"""

    def __init__(
        self,
        config=None,
        source_address=None,
        timeout=10,
        shutdown_event=None,
        verify=True,
    ):
        self.config = {}

        self._source_address = source_address
        self._timeout = timeout
        self._opener = build_opener(source_address, timeout, verify=verify)
        self._verify = verify

        self._shutdown_event = shutdown_event

        self.get_config()
        if config is not None:
            self.config.update(config)

        self.servers = []
        self._best = {}

        self.results = SpeedtestResults(
            client=self.config["client"],
            opener=self._opener,
        )

    @property
    def best(self):
        if not self._best:
            self.get_best_server()
        return self._best

    def get_config(self):
        """Download the speedtest.net configuration and return only the data
        we are interested in
        """

        headers = {}
        if gzip:
            headers["Accept-Encoding"] = "gzip"
        request = build_request(
            "https://www.speedtest.net/speedtest-config.php", headers=headers
        )

        try:
            uh, e = catch_request(request, opener=self._opener)
            if e:
                raise ConfigRetrievalError(e)

            with get_response_stream(uh) as stream:
                try:
                    configxml = stream.read()
                except (OSError, EOFError) as exc:
                    raise ConfigRetrievalError() from exc
        finally:
            uh.close()

        if int(uh.code) != 200:
            return None

        printer(f"Config XML:\n{configxml}", debug=True)

        try:
            root = ET.fromstring(configxml)
        except ET.ParseError as exc:
            raise SpeedtestConfigError("Malformed speedtest.net configuration") from exc
        server_config = root.find("server-config").attrib
        download = root.find("download").attrib
        upload = root.find("upload").attrib
        # times = root.find('times').attrib
        client = root.find("client").attrib

        ignore_servers = [int(i) for i in server_config["ignoreids"].split(",") if i]

        ratio = int(upload["ratio"])
        upload_max = int(upload["maxchunkcount"])
        up_sizes = [32768, 65536, 131072, 262144, 524288, 1048576, 7340032]
        sizes = {
            "upload": up_sizes[ratio - 1 :],
            "download": [350, 500, 750, 1000, 1500, 2000, 2500, 3000, 3500, 4000],
        }

        size_count = len(sizes["upload"])

        upload_count = int(math.ceil(upload_max / size_count))

        counts = {"upload": upload_count, "download": int(download["threadsperurl"])}

        threads = {
            "upload": int(upload["threads"]),
            "download": int(server_config["threadcount"]) * 2,
        }

        length = {
            "upload": int(upload["testlength"]),
            "download": int(download["testlength"]),
        }

        self.config.update(
            {
                "client": client,
                "ignore_servers": ignore_servers,
                "sizes": sizes,
                "counts": counts,
                "threads": threads,
                "length": length,
                "upload_max": upload_count * size_count,
            }
        )

        printer(f"Config:\n{self.config!r}", debug=True)

        return self.config

    def get_servers(self, servers=None, exclude=None, search=None, limit=10):
        """Retrieve a the list of speedtest.net servers, optionally filtered
        to servers matching those specified in the ``servers`` argument
        """
        if servers is None:
            servers = []

        if exclude is None:
            exclude = []

        self.servers.clear()

        for server_list in (servers, exclude):
            for i, s in enumerate(server_list):
                try:
                    server_list[i] = int(s)
                except ValueError as exc:
                    raise InvalidServerIDType(
                        f"{s} is an invalid server type, must be int"
                    ) from exc

        url = "https://www.speedtest.net/api/js/servers"
        urlq = {
            "engine": "js",
            "https_functional": "true",
            "limit": limit,
        }
        if search:
            urlq["search"] = search
        url = f"{url}?{urlencode(urlq)}"

        headers = {}
        if gzip:
            headers["Accept-Encoding"] = "gzip"

        errors = []
        try:
            request = build_request(
                url,
                headers=headers,
            )
            uh, e = catch_request(request, opener=self._opener)
            if e:
                errors.append(f"{e}")
                raise ServersRetrievalError()

            stream = get_response_stream(uh)

            try:
                serversjson = json.load(stream)
            except ValueError as exc:
                raise SpeedtestServersError() from exc

            stream.close()
            uh.close()

            if int(uh.code) != 200:
                raise ServersRetrievalError()

            printer(f"Servers JSON:\n{serversjson}", debug=True)

            for server in serversjson:
                if (
                    int(server.get("id")) in self.config["ignore_servers"]
                    or int(server.get("id")) in exclude
                ):
                    continue

                self.servers.append(server)

        except ServersRetrievalError:
            pass

        if (servers or exclude) and not self.servers:
            raise NoMatchedServers()

        return self.servers

    def get_best_server(self):
        """Perform a speedtest.net "ping" to determine which speedtest.net
        server has the lowest latency
        """

        if self._source_address:
            source_address_tuple = (self._source_address, 0)
        else:
            source_address_tuple = None

        user_agent = build_user_agent()

        def test_latency(server):
            result = 3600
            host = f"{server['host']}"
            latency_url = f"https://{host}/latency.txt"
            printer(f"GET {latency_url}", debug=True)
            try:
                h = SpeedtestHTTPSConnection(
                    host,
                    source_address=source_address_tuple,
                    verify=self._verify,
                    timeout=self._timeout,
                )
                headers = {"User-Agent": user_agent}
                h.request("GET", latency_url, headers=headers)
                start = timeit.default_timer()
                with h.getresponse() as r:
                    text = r.read(9)
                    if int(r.status) == 200 and text == b"test=test":
                        result = timeit.default_timer() - start
            except HTTP_ERRORS as exc:
                printer(f"ERROR: {exc!r}", debug=True)

            return result

        results = {}
        with ThreadPoolExecutor() as executor:
            ping_each_n_times = 3
            iter_1 = repeat_elements(self.servers, ping_each_n_times)
            iter_2 = copy(iter_1)
            for server, latency in zip(iter_1, executor.map(test_latency, iter_2)):
                if server["id"] not in results:
                    results[server["id"]] = []
                results[server["id"]].append(latency)

        for server in results:
            latency = results[server]
            results[server] = round((sum(latency) / (len(latency) * 2)) * 1000, 3)
            server_idx = next(
                idx for idx, s in enumerate(self.servers) if s["id"] == server
            )
            self.servers[server_idx]["latency"] = results[server]
        self.servers.sort(key=lambda s: s["latency"])

        best = self.servers[0]
        self.results.ping = best["latency"]
        self.results.server = best

        self._best.update(self.servers[0])

        printer(f"Best Server:\n{best!r}", debug=True)
        printer(f"Sorted Servers:\n{self.servers!r}", debug=True)
        return best

    def download(self, callback=do_nothing, threads=None):
        """Test download speed against speedtest.net

        A ``threads`` value of ``None`` will fall back to those dictated
        by the speedtest.net configuration
        """

        urls = []
        for size in self.config["sizes"]["download"]:
            for _ in range(0, self.config["counts"]["download"]):
                urls.append(f"https://{self.best['host']}/random{size}x{size}.jpg")

        request_count = len(urls)
        requests = []
        for url in urls:
            requests.append(build_request(url))

        max_threads = threads or self.config["threads"]["download"]
        in_flight = {"threads": 0}

        def producer(q, requests, request_count):
            for i, request in enumerate(requests):
                thread = HTTPDownloader(
                    i,
                    request,
                    start,
                    self.config["length"]["download"],
                    opener=self._opener,
                    shutdown_event=self._shutdown_event,
                )
                while in_flight["threads"] >= max_threads:
                    time.sleep(0.001)
                catch_thread_operation(
                    shutdown_event=self._shutdown_event,
                    target=thread.start,
                )
                q.put(thread, True)
                in_flight["threads"] += 1
                callback(i, request_count)

        finished = []

        def consumer(q: Queue, request_count):
            while len(finished) < request_count:
                thread = q.get(True)
                catch_thread_operation(
                    shutdown_event=self._shutdown_event,
                    target=thread.join,
                )
                in_flight["threads"] -= 1
                finished.append(sum(thread.result))
                callback(thread.i, request_count, end=True)

        q = Queue(max_threads)
        prod_thread = threading.Thread(
            target=producer, args=(q, requests, request_count)
        )
        cons_thread = threading.Thread(target=consumer, args=(q, request_count))
        start = timeit.default_timer()
        threads = (prod_thread, cons_thread)
        for thread in threads:
            catch_thread_operation(
                shutdown_event=self._shutdown_event,
                target=thread.start,
            )
        for thread in threads:
            catch_thread_operation(
                shutdown_event=self._shutdown_event,
                target=thread.join,
            )

        stop = timeit.default_timer()
        self.results.bytes_received = sum(finished)
        self.results.download = (self.results.bytes_received / (stop - start)) * 8.0
        if self.results.download > 100000:
            self.config["threads"]["upload"] = 8
        return self.results.download

    def upload(self, callback=do_nothing, pre_allocate=True, threads=None):
        """Test upload speed against speedtest.net

        A ``threads`` value of ``None`` will fall back to those dictated
        by the speedtest.net configuration
        """

        sizes = []

        for size in self.config["sizes"]["upload"]:
            for _ in range(0, self.config["counts"]["upload"]):
                sizes.append(size)

        # request_count = len(sizes)
        request_count = self.config["upload_max"]

        requests = []
        for size in sizes:
            # We set ``0`` for ``start`` and handle setting the actual
            # ``start`` in ``HTTPUploader`` to get better measurements
            data = HTTPUploaderData(
                size,
                0,
                self.config["length"]["upload"],
                shutdown_event=self._shutdown_event,
            )
            if pre_allocate:
                data.pre_allocate()

            headers = {"Content-length": size}
            requests.append(
                (
                    build_request(
                        f"https://{self.best['host']}/upload.php", data, headers=headers
                    ),
                    size,
                )
            )

        max_threads = threads or self.config["threads"]["upload"]
        in_flight = {"threads": 0}

        def producer(q, requests, request_count):
            for i, request in enumerate(requests[:request_count]):
                thread = HTTPUploader(
                    i,
                    request[0],
                    start,
                    request[1],
                    self.config["length"]["upload"],
                    opener=self._opener,
                    shutdown_event=self._shutdown_event,
                )
                while in_flight["threads"] >= max_threads:
                    time.sleep(0.001)
                catch_thread_operation(
                    shutdown_event=self._shutdown_event,
                    target=thread.start,
                )
                q.put(thread, True)
                in_flight["threads"] += 1
                callback(i, request_count)

        finished = []

        def consumer(q: Queue, request_count):
            while len(finished) < request_count:
                thread = q.get(True)
                catch_thread_operation(
                    shutdown_event=self._shutdown_event,
                    target=thread.join,
                )
                in_flight["threads"] -= 1
                finished.append(thread.result)
                callback(thread.i, request_count, end=True)

        q = Queue(threads or self.config["threads"]["upload"])
        prod_thread = threading.Thread(
            target=producer, args=(q, requests, request_count)
        )
        cons_thread = threading.Thread(target=consumer, args=(q, request_count))
        start = timeit.default_timer()
        threads = (prod_thread, cons_thread)
        for thread in threads:
            catch_thread_operation(
                shutdown_event=self._shutdown_event,
                target=thread.start,
            )
        for thread in threads:
            catch_thread_operation(
                shutdown_event=self._shutdown_event,
                target=thread.join,
            )

        stop = timeit.default_timer()
        self.results.bytes_sent = sum(finished)
        self.results.upload = (self.results.bytes_sent / (stop - start)) * 8.0
        return self.results.upload


def ctrl_c(shutdown_event):
    """Catch Ctrl-C key sequence and set a SHUTDOWN_EVENT for our threaded
    operations
    """

    def inner(_signum, _frame):
        shutdown_event.set()
        printer("\nCancelling...", error=True)
        sys.exit(0)

    return inner


def version():
    """Print the version"""
    printer(f"speedtest-cli {__version__}")
    printer("Python %s" % sys.version.replace("\n", ""))
    sys.exit(0)


def csv_header(delimiter=","):
    """Print the CSV Headers"""
    printer(SpeedtestResults.csv_header(delimiter=delimiter))
    sys.exit(0)


def parse_args():
    """Function to handle building and parsing of command line arguments"""
    description = (
        "Command line interface for testing internet bandwidth using "
        "speedtest.net.\n"
        "------------------------------------------------------------"
        "--------------\n"
        "https://github.com/sivel/speedtest-cli"
    )

    parser = ArgParser(description=description)
    parser.add_argument(
        "--no-download",
        dest="download",
        default=True,
        action="store_const",
        const=False,
        help="Do not perform download test",
    )
    parser.add_argument(
        "--no-upload",
        dest="upload",
        default=True,
        action="store_const",
        const=False,
        help="Do not perform upload test",
    )
    parser.add_argument(
        "--single",
        default=False,
        action="store_true",
        help="Only use a single connection instead of "
        "multiple. This simulates a typical file "
        "transfer.",
    )
    parser.add_argument(
        "--bytes",
        dest="units",
        action="store_const",
        const=("byte", 8),
        default=("bit", 1),
        help="Display values in bytes instead of bits. Does "
        "not affect the image generated by --share, nor "
        "output from --json or --csv",
    )
    parser.add_argument(
        "--share",
        action="store_true",
        help="Generate and provide a URL to the speedtest.net "
        "share results image, not displayed with --csv",
    )
    parser.add_argument(
        "--simple",
        action="store_true",
        default=False,
        help="Suppress verbose output, only show basic information",
    )
    parser.add_argument(
        "--csv",
        action="store_true",
        default=False,
        help="Suppress verbose output, only show basic "
        "information in CSV format. Speeds listed in "
        "bit/s and not affected by --bytes",
    )
    parser.add_argument(
        "--csv-delimiter",
        default=",",
        type=str,
        help="Single character delimiter to use in CSV " 'output. Default ","',
    )
    parser.add_argument(
        "--csv-header", action="store_true", default=False, help="Print CSV headers"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        default=False,
        help="Suppress verbose output, only show basic "
        "information in JSON format. Speeds listed in "
        "bit/s and not affected by --bytes",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="Display a list of speedtest.net servers sorted by distance",
    )
    parser.add_argument(
        "--limit",
        default=10,
        type=int,
        help="Maximum number of servers to get. Default 10",
    )
    parser.add_argument(
        "--server",
        type=int,
        action="append",
        help="Specify a server ID to test against. Can be supplied multiple times",
    )
    parser.add_argument(
        "--search",
        type=str,
        action="store",
        nargs="*",
        help="Search for a server with the provided string in the name",
    )
    parser.add_argument(
        "--exclude",
        type=int,
        action="append",
        help="Exclude a server from selection. Can be supplied multiple times",
    )
    parser.add_argument("--source", help="Source IP address to bind to")
    parser.add_argument(
        "--timeout",
        default=5,
        type=float,
        help="HTTP timeout in seconds. Default 5",
    )
    parser.add_argument(
        "--no-verify",
        default=True,
        dest="verify",
        action="store_false",
        help="Do not verify SSL certs. Default True",
    )
    parser.add_argument(
        "--no-pre-allocate",
        dest="pre_allocate",
        action="store_const",
        default=True,
        const=False,
        help="Do not pre allocate upload data. Pre allocation "
        "is enabled by default to improve upload "
        "performance. To support systems with "
        "insufficient memory, use this option to avoid a "
        "MemoryError",
    )
    parser.add_argument(
        "--version", action="store_true", help="Show the version number and exit"
    )
    parser.add_argument(
        "--debug", action="store_true", help=ARG_SUPPRESS, default=ARG_SUPPRESS
    )

    options = parser.parse_args()
    return options


def printer(string, quiet=False, debug=False, error=False, **kwargs):
    """Helper function print a string with various features"""

    if debug and not DEBUG:
        return

    if debug:
        if sys.stdout.isatty():
            out = f"\x1b[1;30mDEBUG: {string}\x1b[0m"
        else:
            out = f"DEBUG: {string}"
    else:
        out = string

    if error:
        kwargs["file"] = sys.stderr

    if not quiet:
        print(out, **kwargs)


def shell():
    """Run the full speedtest.net test"""

    global DEBUG
    shutdown_event = threading.Event()

    signal.signal(signal.SIGINT, ctrl_c(shutdown_event))

    args = parse_args()

    # Print the version and exit
    if args.version:
        version()

    if not args.download and not args.upload:
        raise SpeedtestCLIError("Cannot supply both --no-download and --no-upload")

    if len(args.csv_delimiter) != 1:
        raise SpeedtestCLIError("--csv-delimiter must be a single character")

    if args.csv_header:
        csv_header(args.csv_delimiter)

    debug = getattr(args, "debug", False)
    if debug == "SUPPRESSHELP":
        debug = False
    if debug:
        DEBUG = True

    quiet = args.simple or args.csv or args.json
    machine_format = args.csv or args.json

    if args.search:
        args.search = " ".join(args.search)

    # Don't set a callback if we are running quietly
    if quiet or debug:
        callback = do_nothing
    else:
        callback = print_dots(shutdown_event)

    printer("Retrieving speedtest.net configuration...", quiet)
    try:
        speedtest = Speedtest(
            source_address=args.source,
            timeout=args.timeout,
            verify=args.verify,
            shutdown_event=shutdown_event,
        )
    except (*HTTP_ERRORS, ConfigRetrievalError) as exc:
        printer("Cannot retrieve speedtest configuration", error=True)
        raise SpeedtestCLIError() from exc

    if args.list:
        try:
            speedtest.get_servers(search=args.search, limit=args.limit)
        except (*HTTP_ERRORS, ServersRetrievalError) as exc:
            printer("Cannot retrieve speedtest server list", error=True)
            raise SpeedtestCLIError() from exc

        for server in sorted(speedtest.servers, key=lambda s: s["distance"]):
            line = (
                "%(id)5s) %(sponsor)s (%(name)s, %(country)s) "
                "[%(distance)d mi]" % server
            )
            try:
                printer(line)
            except OSError as exc:
                if exc.errno != errno.EPIPE:
                    raise
        sys.exit(0)

    printer(
        f"Testing from {speedtest.config['client']['isp']} ({speedtest.config['client']['ip']})...",
        quiet,
    )

    printer("Retrieving speedtest.net server list...", quiet)
    try:
        speedtest.get_servers(
            servers=args.server,
            exclude=args.exclude,
            search=args.search,
            limit=args.limit,
        )
    except NoMatchedServers as exc:
        raise SpeedtestCLIError(
            "No matched servers: %s" % ", ".join("%s" % s for s in args.server)
        ) from exc
    except (*HTTP_ERRORS, ServersRetrievalError) as exc:
        printer("Cannot retrieve speedtest server list", error=True)
        raise SpeedtestCLIError() from exc
    except InvalidServerIDType as exc:
        raise SpeedtestCLIError(
            "%s is an invalid server type, must "
            "be an int" % ", ".join("%s" % s for s in args.server)
        ) from exc

    if args.server and len(args.server) == 1:
        printer("Retrieving information for the selected server...", quiet)
    else:
        printer("Selecting best server based on ping...", quiet)
    speedtest.get_best_server()

    results = speedtest.results

    printer(
        "Hosted by %(sponsor)s (%(name)s) [%(distance)d mi]: "
        "%(latency)s ms" % results.server,
        quiet,
    )

    if args.download:
        printer("Testing download speed", quiet, end=("", "\n")[bool(debug)])
        speedtest.download(callback=callback, threads=(None, 1)[args.single])
        printer(
            "Download: %0.2f M%s/s"
            % ((results.download / 1000.0 / 1000.0) / args.units[1], args.units[0]),
            quiet,
        )
    else:
        printer("Skipping download test", quiet)

    if args.upload:
        printer("Testing upload speed", quiet, end=("", "\n")[bool(debug)])
        speedtest.upload(
            callback=callback,
            pre_allocate=args.pre_allocate,
            threads=(None, 1)[args.single],
        )
        printer(
            "Upload: %0.2f M%s/s"
            % ((results.upload / 1000.0 / 1000.0) / args.units[1], args.units[0]),
            quiet,
        )
    else:
        printer("Skipping upload test", quiet)

    printer(f"Results:\n{results.dict()!r}", debug=True)

    if not args.simple and args.share:
        results.share()

    if args.simple:
        printer(
            "Ping: %s ms\nDownload: %0.2f M%s/s\nUpload: %0.2f M%s/s"
            % (
                results.ping,
                (results.download / 1000.0 / 1000.0) / args.units[1],
                args.units[0],
                (results.upload / 1000.0 / 1000.0) / args.units[1],
                args.units[0],
            )
        )
    elif args.csv:
        printer(results.csv(delimiter=args.csv_delimiter))
    elif args.json:
        printer(results.json())

    if args.share and not machine_format:
        printer(f"Share results: {results.share()}")


def main():
    try:
        shell()
    except KeyboardInterrupt:
        printer("\nCancelling...", error=True)


if __name__ == "__main__":
    main()
