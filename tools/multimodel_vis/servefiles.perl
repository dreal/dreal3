#!/usr/bin/env perl
#
# This script basically checks to see if you have Python 2.x or Python
# 3.x and passes the correct params to start up a web server.

use strict;
use warnings;

use FindBin;

my $www_dir = $FindBin::Bin . "/";
print("Serving files from: $www_dir\n");
chdir($www_dir);

my @server_cmd =
  ( "python",
  );

my $python_ver = `python --version 2>&1`;
if ($python_ver =~ /^python\s+3\.\d+\.\d+$/i) {
  print("Looks like you have Python 3.\n");
  push(@server_cmd, "-m", "http.server");
}
elsif ($python_ver =~ /^python\s+2\.\d+\.\d+$/i) {
  print("Looks like you have Python 2.\n");
  push(@server_cmd, "-m", "SimpleHTTPServer");
}
else {
  die ("Couldn't determine your Python version: $python_ver");
}

print("Starting server, navigate to: http://localhost:8000\n");
exec(@server_cmd);

