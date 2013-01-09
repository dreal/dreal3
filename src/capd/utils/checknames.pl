#!/usr/bin/perl

# This script verifies whether the uniqueness property of source code file
# names is satisfied, as required in the CAPD library.
# Just run this script from the current location, and it will display
# appropriate messages and explanations if necessary.

# Initial version written by Pawel Pilarczyk on April 4, 2005.
# Modifications: [add your name here]

# Copyright (C) 2005 by the CAPD Group.
#
# This is free software; you can redistribute it and/or modify it under the
# terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or any later version.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this software; see the file "license.txt".  If not, write to the
# Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
# MA 02111-1307, USA.

print "Checking the uniqueness of source code file names...\n";

# create a dictionary which stores the original directories of all the files
my %files;

# go one directory level up if started in the 'utils' directory
chdir '..' unless -e 'include' && -e 'src';

# create the list of all the directories to check
my @basedirs = ('include', 'src', 'examples', 'tests', 'programs', 'private');
my @dirs = ();
foreach (@basedirs)
{
	@dirs = (@dirs, glob "$_/*");
}

my %cpp;
my %hpp;

my %dirnames;
my %dir;

foreach my $dir (@dirs)
{
	next if $dir =~ m[/CVS$];
	next unless -d $dir;
	foreach my $file (glob ("$dir/*.cpp"), glob ("$dir/*.h"), glob ("$dir/*.hpp"))
	{
		my $name = $file;
		$name =~ s[$dir/][];
		if ($files{$name})
		{
			if ($name =~ m/\.cpp$/)
			{
				$cpp{$name} ++;
			}
			else
			{
				$hpp{$name} ++;
			}
			$files{$name} .= ' ';
		}
		$files{$name} .= $dir;
	}

	next if $dir =~ m[^include/];
	my $name = $dir;
	$name =~ s[^.*/][];
	if ($dirnames{$name})
	{
		$dir{$name} ++;
		$dirnames{$name} .= ' ';
	}
	$dirnames{$name} .= $dir;
}

foreach my $name (keys %hpp)
{
	print "WARNING: $name exists in $files{$name}.\n";
}
foreach my $name (keys %cpp)
{
	print "PROBLEM: $name exists in $files{$name}.\n";
}
print <<"WARNING" if keys %cpp or keys %hpp;
The above warnings do not imply serious errors, but they indicate
that it may be impossible to group all the files in one directory.
WARNING

foreach my $name (keys %dir)
{
	print "ERROR: $name is ambiguous: $dirnames{$name}.\n";
}
print <<"PROBLEM" if keys %dir;
The above messages indicate serious errors. This situation must be fixed
by renaming some directories, or otherwise the compilation results
may be erroneous.
PROBLEM

# display the OK message if appropriate
print "No problems detected.\n" unless keys %hpp or keys %cpp or keys %dir;

