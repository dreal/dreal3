# This is a PERL script to adjust the command line for the Turbo Librarian.
# It is used by some makefiles. Copyright (C) 2004 by the CAPD group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Created on November 16, 2004 by PwP. Last revision: November 17, 2004.

# determine whether to use '+' (add to library) or '+-' (replace in library)
my $plus = '+';
$plus = $plus . '-' if -r $ARGV[0];

# change slashes to backslashes in all the arguments
foreach (@ARGV) {
	s(/)(\\)g;
}

# add a plus to all the object file names
for (my $n = 1; $n < @ARGV; $n ++) {
	$ARGV[$n] = $plus . $ARGV[$n];
}
	
# prepare an appropriate command line to create the library
my $c = 'tlib /C /P256 ' . join (' ', @ARGV);

# print the command line, execute it and show the output
print $c, "\n";
@tab = `$c`;
$result = $? >> 8;
print @tab;

END
{
	$? = $result;
}

