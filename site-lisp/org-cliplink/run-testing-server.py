#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import ssl
from threading import Thread, Lock
import time

import SimpleHTTPServer
import BaseHTTPServer

from request_handlers import GzipSimpleHTTPServer, SimpleAuthHandler

log_mutex = Lock()


def log(message):
    log_mutex.acquire()
    try:
        print message
    finally:
        log_mutex.release()


def start_http_server(port):
    log("(%d) Starting HTTP Server..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), SimpleHTTPServer.SimpleHTTPRequestHandler)
    httpd.serve_forever()


def start_https_server(port, certificate):
    log("(%d) Starting HTTPS Server..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), SimpleHTTPServer.SimpleHTTPRequestHandler)
    httpd.socket = ssl.wrap_socket(httpd.socket, certfile=certificate, server_side=True)
    httpd.serve_forever()


def start_gziped_http_server(port):
    log("(%d) Starting Gziped HTTP Server..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), GzipSimpleHTTPServer)
    httpd.serve_forever()


def start_gziped_https_server(port, certificate):
    log("(%d) Starting Gziped HTTPS Server..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), GzipSimpleHTTPServer)
    httpd.socket = ssl.wrap_socket(httpd.socket, certfile=certificate, server_side=True)
    httpd.serve_forever()


def start_http_server_with_basic_auth(port):
    log("(%d) Starting HTTP Server with Basic Auth..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), SimpleAuthHandler)
    httpd.serve_forever()


def start_https_server_with_basic_auth(port, certificate):
    log("(%d) Starting HTTPS Server with Basic Auth..." % port)
    httpd = BaseHTTPServer.HTTPServer(("", port), SimpleAuthHandler)
    httpd.socket = ssl.wrap_socket(httpd.socket, certfile=certificate, server_side=True)
    httpd.serve_forever()

if __name__ == "__main__":
    script_location = os.path.dirname(os.path.abspath(__file__))
    site_location = os.path.join(script_location, "test-data", "site")
    certfile = os.path.join(script_location, "test-data", "certificates", "self-ssl.pem")
    os.chdir(site_location)

    print "Serving", os.getcwd(), "directory"

    server_threads = [Thread(target = start_http_server, args = (8001,)),
                      Thread(target = start_https_server, args = (4443, certfile)),
                      Thread(target = start_gziped_http_server, args = (8002,)),
                      Thread(target = start_gziped_https_server, args = (4444, certfile)),
                      Thread(target = start_http_server_with_basic_auth, args = (8003,)),
                      Thread(target = start_https_server_with_basic_auth, args = (4445, certfile))]

    for thread in server_threads:
        thread.daemon = True
        thread.start()

    # This loop allows you to ^C when you run this script standalone
    while True:
        time.sleep(1)
