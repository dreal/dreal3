# This is a PERL script to change slashes to backslashes in a command line.
# It is used by some makefiles. Copyright (C) 2004 by the CAPD group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Created on November 17, 2004 by PwP. Last revision: November 17, 2004.

# change slashes to backslashes in all the arguments
foreach (@ARGV) {
	s(/)(\\)g;
}

# glue the command line words together
my $c = join (' ', @ARGV);

# print the command line, execute it and show the output
if ($c =~ m/^rem /)
{
	$result = 0;
}
else
{
	print $c, "\n";
	@tab = `$c`;
	$result = $? >> 8;
	print @tab;
}

END
{
	$? = $result;
}

