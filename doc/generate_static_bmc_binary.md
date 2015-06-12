To generate a static binary of bmc, please do the followings:

 - Uncomment [line 52 of dreal3/tools/_oasis file](https://github.com/dreal/dreal3/blob/master/tools/_oasis#L52)
  by removing `#` from the line `# CCLib: -static`.
 - Execute `cd dreal3/tools && make dist-clean && make`.

During the building process, you will get warnings such as

    /usr0/home/your_name/.opam/4.02.1/lib/ocaml/libunix.a(getaddrinfo.o):getaddrinfo.c:function unix_getaddrinfo:
    warning: Using 'getaddrinfo' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking

It indicates that there are certain functions which still require the
shared libraries during the runtime if used. Fortunately, we don't use
those functions and you can simply ignore those warnings. You can find
details about this warning at http://stackoverflow.com/a/3087067.

Note that it does not work on OS X. See http://stackoverflow.com/a/3801032 for details.
