# Create Doxygen/License headers for all the files whose names with subdirs
# are given at the command line. Written for the CAPD library files.
# PwP, Feb 17-24, 2005.

# How to use this program:
# - put the file 'template.h' in the current directory
# - run this program with the arguments */*.h */*.cpp
# The program prepends the template to all these files
# and appends the last non-empty line of the template to them.
# It replaces the argument of "@addtogroup" with the highest-level
# subdirectory name and "@file"'s argument with the actual file name.

# read the template file
open (TEMPLATE, "template.h") or die "The file 'template.h' is missing.";
@template = <TEMPLATE>;
close (TEMPLATE);

# extract the beginning and the ending of the template
pop (@template) while ($template [-1] eq "\n");
my $end = pop @template;
pop (@template) while (($template [-1] eq "\n") ||
	($template [-1] =~ /Na samym koncu pliku/));
my $beg = join ('', @template);

# add the header to the given file;
# arguments: file name, header, footer
sub addheader
{
	my $filename = shift;
	return unless -f $filename;
	my $beg = shift;
	my $end = shift;

	# split the filename to the path name and the actual file name
	$filename =~ m [([^/]*).*?([^/]+)];
	my $package = $1;
	my $file = $2;
	return if ($filename eq '') && ($package eq '');

	# replace the package and file names in the header
	$beg =~ s/\@addtogroup.*?\n/\@addtogroup $package\n/;
	$beg =~ s/\@file.*?\n/\@file $file\n/;
	
	# read the entire file
	open (FILE, $filename) or die "Unable to open '$filename'.";
	my @lines = <FILE>;
	close (FILE);

	# remove empty lines at the beginning and at the end of the file
	shift (@lines) while ($lines [0] eq "\n");
	pop (@lines) while ($lines [-1] eq "\n");
	
	# write the new file
	open (FILE, ">$filename");
	print FILE "$beg\n";
	foreach (@lines)
	{
		print FILE;
	}
	print FILE "\n$end";
	close (FILE);
}

# add the header and footer to each file
foreach my $filemask (@ARGV)
{
	while (my $filename = glob $filemask)
	{
		addheader ($filename, $beg, $end);
	}
}

