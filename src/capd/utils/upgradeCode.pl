#!/usr/bin/perl -w

# default values
my $changesDataFile = 'fileNamesIncludesChanges.txt';
my $classesChangesDataFile = 'classNamesChanges.txt';
my $directory = "..";
my $includeDirectory = "../include/";

sub help{
print <<END_OF_HELP;
usage: upgradeCode [options] 

It corrects paths in include directives in C++ files

Possible options [and its default values]:
  -f fileNamesChanges            [$changesDataFile]
  -c classNamesChanges           [$classesChangesDataFile]
  -d directory                   [$directory]
  -i includeDirectory            [$includeDirectory]

In every file (.cpp, .h, .hpp) in directory 'directory' and subdirectories 
it updates 'includes' according to file 'fileNamesChanges'
It also checks if new file name is correct 
i.e. if given file is in 'includeDirectory'.
If -c is specified then it corrects class names according to file 
'classNamesChanges'. (By default this option is disabled).
END_OF_HELP
}

my %fileNames = ();
my @includesToBeRemoved = ();
my %classesNames = ();
my $changeClasses = 0;

sub processLine{
  my $line = $_[0];
  if( $line =~ /^\s*#\s*include\s*"([^"]*)"/){
    my $path = $1;
    my $newPath = $path;
    if($fileNames{$path}){
        $newPath = $fileNames{$path};
    }
    else{
      if( $path =~ /^\s*(\.\.\/)?\.\.\/src\/(.*)/){
        $newPath = '../src/capd/'.$+;
      }
      else{
        $newPath = 'capd/'.$path;
      }
      my $header = $includeDirectory.$newPath;
       
      if(!( -e $header)){
#        print "\n$path __________________ $newPath \n $header \n";
        $newPath = $path;    
        
      }
    }
    if($newPath ne $path){
      print "\n $path => $newPath ";
      $line =~ s/$path/$newPath/;
    }
    
  }
  if($changeClasses){
  while (($key,$value) = each %classesNames){
     # print "\n Want to change $key ==> $value";
      if($line =~ s/^$key/$value/g){
         print "\n class name change: $key ==> $value";
      } 
      if($line =~ s/(\s)$key/$1$value/g){
         print "\n class name change: $key ==> $value";
      } 
    }
  }
  return $line;
}
    

sub processFile {
  my $name = $_[0];
  open(IN, '<', $name);
  my @file_in = <IN>;
  close IN;
  system('cp', $name, $name.'.bak');
  open(OUT, '>', $name);
  foreach $line (@file_in){
#    print $line;
      print OUT processLine($line);
  }
}

sub processDir{
  my $dirName = $_[0];
  opendir(DIR, $dirName);
  my @files = readdir(DIR);
  close DIR;
  my @dirsNames;
  foreach my $file (@files){
    $fullFileName = $dirName.'/'.$file;
    if(($file =~ /\.c(pp)?$/) || ($file =~ /\.h(pp)?$/)){
      print "\n  processing file: $file";
      processFile($fullFileName);
 
    }
    if((-d $fullFileName) && ($file ne '..') && ($file ne '.')){
       push @dirsNames, $fullFileName;
    }
  }
  foreach $dir (@dirsNames){
    print "\nentering directory $dir";
    processDir($dir);
  }
}

sub createPathData{
    open (FILE, '<', $changesDataFile);
    my @names = <FILE>;
    close FILE;
    foreach $line (@names){
      if($line =~ /\s*(\S+)\s+(\S+)\s+(\S*)/){   
        my $action = $1;
        if($1 eq '#') { next;}
        my $oldName = $2; 
        my $newName = $3;
        if(($action eq 'D') && ($newName eq '')){
           push @includesToBeRemoved, $oldName;
           next;
        }
        if($oldName =~ /^include\/(\S+)/) {
          my $fileName = $1;
          if($newName =~ /^include\/(\S+)/){
            $fileNames {$fileName} = $1;
          }
# if uncommented it also changes path with added 'capd'
#   usefull if further changes need to be done but it also generate errors 
#   due to scheme NameIntf.h => Name.h => Name.hpp
#         
#          $fileNames{'capd/'.$fileName} = $1;
        }
        else{
          
            $fileNames{'../'.$oldName} = '../'.$newName;
          
#          $fileNames{'../src/capd/'.$fileName} = '../'.$1;
        }  
      }
    } 
}

sub createClassData{
    open (FILE, '<', $classesChangesDataFile);
    my @names = <FILE>;
    close FILE;
    foreach $line (@names){
      if($line =~ /^\s*#/) { next;}
      if($line =~ /\s*(\S.*\S)\s+==>\s+(\S.*\S)/){   
        
        my $oldName = $1; 
        my $newName = $2;
        $classesNames{$oldName} = $newName;
      }
    }
}
          
if ($#ARGV >= 0){   
  my $label = 'f';
  my %params = ();
  foreach $argument (@ARGV){
    if($argument =~ /^-(.+)/){
      $label = $1;
      $changeClasses = 1 if($label eq 'c');
    }
    else{
      $params{$label} = $argument;
    }
  }

  $changesDataFile = $params{f} if($params{f});
  $classesChangesDataFile = $params{c}  if($params{c});
    
  if($params{d}){
    $directory = $params{d};
    if($directory =~ /(.+)\/$/){
        $directory = $1;
    }
  }
  if($params{d}){ 
    $includeDirectory = $params{i};
    if(!($includeDirectory =~ /\/$/)){
      $includeDirectory = $includeDirectory.'/';
    }
  }
    
  
  createPathData();
  createClassData();
  processDir($directory);
print "directory = $directory";
}else{
  help();
}
print "\n";
