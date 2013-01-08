# This is a PERL script to adjust the command line for the Turbo C++ Compiler.
# It is used by some makefiles. Copyright (C) 2004 by the CAPD group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Created on November 17, 2004 by PwP. Last revision: November 17, 2004.

# change slashes to backslashes in all the arguments
foreach (@ARGV) {
	s(/)(\\)g;
}

# prepare an appropriate command line to compile the file
my $c = 'bcc32 -O -k -tWM -tW -vi -w -w-inl ' . join (' ', @ARGV);

# print the command line, execute it and show the output
print $c, "\n";
@tab = `$c`;
$result = $? >> 8;
print @tab;

END
{
	$? = $result;
}

