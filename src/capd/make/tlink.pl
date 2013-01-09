# This is a PERL script to adjust the command line for the Incremental Linker.
# It is used by some makefiles. Copyright (C) 2004 by the CAPD group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Created on November 16, 2004 by PwP. Last revision: November 17, 2004.

# change slashes to backslashes in all the arguments
foreach (@ARGV) {
	s(/)(\\)g;
}

# determine the name of the EXE file (ignore the preceding '-o')
my $exefile = $ARGV [1];

# determine all the object files
my $objfiles = '';
for (my $n = 2; $n <= $#ARGV; $n ++)
{
	last if $ARGV [$n] =~ /.lib$/;
	$objfiles .= ' ' if $objfiles;
	$objfiles .= $ARGV [$n];
}

# determine the names of the libraries
my $library = '';
while ($ARGV[-1] =~ /.lib$/)
{
	$library .= ' ' if $library;
	$library .= $ARGV[-1];
	$#ARGV --;
}

# create an appropriate command line to link the program
my $c = 'ilink32 -Tpe -x -Gn -c c0x32.obj ' . $objfiles . ',' . $exefile .
	',,' . $library . ' cw32.lib import32.lib';

# print the command line, execute it and show the output
print $c, "\n";
@tab = `$c`;
$result = $? >> 8;
print @tab;

END
{
	$? = $result;
}


