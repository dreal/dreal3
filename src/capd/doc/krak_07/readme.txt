######################## KRAK package #####################################
(c) Marian Mrozek, Kraków/Atlanta 1992-

   KRAK package resulted in an attempt to obtain a graphical programming
enviroment independent of a particular hardware and operating system.
It is built around a relatively small kernel and only the kernel
functions must be implemented for a particular system.
    KRAK is intended to be a simple graphics package for programs in C/C++,
which can be relatively easily implemented on various machines.
It is built over a simple kernel and only the kernel must be rewritten
when the package is transferred to another enviroment or another machine.
The kernel is implemented for INTEL based machines running 
DOS/Windows 3.1/Windows 95 and SUN SPARC machines running SOLARIS. 
A very old implementation for APPLE computers is very much out of date.
   The package enables combining text and graphics, gives control over
keyboard and mouse and includes a simple subwindow system.
   The package is opened by calling the function openGW. This call must
precede all other calls of functions in the package. To ensure proper
termination of the program the function closeGW should be called before exit.
   When openGW is called a graphics window of requested size is opened. Since
the rest of the screen cannot be seen from the package, all future references
to the screen should be understood as references to the graphics window.
   The package uses two coordinate systems. The pixel coordinate system
(in integers) corresponds to the actual pixels of the screen. In this
coordinate system the top left point of the screen has coordinates 
(0,0) and the right bottom corner the coordinates corresponding to the width 
and the height (in pixels) of the screen. The size of the screen
is determined by the user when the package is opened and cannot be changed
later on. 
   The world coordinate system (in double's) is determined by the user by
means of the dscrGW function and can be changed any time.
   Many functions have two versions. The version starting with a capital 
character uses the pixel coordinate system whereas the other version uses
the world coordinate system.
   The kernel for SUN under XWindows is essentially the tool for adding 
graphics to C-programs written by Ron Shonkwiler (with minor changes). The
author gratefully acknowledges his permission to use his software.

   The package was first developed in C and the decsription of this version
is provided in the 
    krak.txt 
file. Gradually an object oriented version came to existence and this version
is briefly described in file
    krak-obj.txt
The documentation is poor, so you would probably like to inspect the code itself.
A brief guide to the files is contained in the file 
    filelist.txt
In the package a very useful class frstring is provided. It gives you 
a very flexible and easy way to manipulate strings. A very short documentation is
in 
    frstring.h
   
>>>>>>> IMPORTANT NOTE:
 Every program using KRAK must #include "krak.h".
 Usually no other #includes are necessary.
