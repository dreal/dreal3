#!/usr/bin/perl

$debug_nazwy = 0;
$debug_kom = 0;
$debug_dok = 0;
$debug_gendok = 0;
$debug_refs = 0;
$debug_funcid = 0;
$debug_nazwwk = 0;
$debug_sub_refs = 0;
$debug_descr = 0;
$debug_seealso = 1;

$dir = "/mnt/dosc/misiek/cpp/krak/so_c/capd/krak5/";
#$dir = "/home/mikolaj/C++/krak/krak5/";
@cfiles = ("frame.cpp", "frame.h", "coord3d.cpp", "coord3d.h");
$class = "Frame";

sub loadrefs()
{
  open(REFS, "<refs.dat");
  while (<REFS>)
  {
    chop;
    $odw=<REFS>;
    chop($odw);
    $refs{$_}=$odw;
    print "$_\n" if $debug_refs == 1;
    
    s/\:\:\w+\s[&\*]?/\:\:/;
    $refs{$_}=$odw;
    print "$_\n" if $debug_refs == 1;
    
    s/^(.*)\(.*$/$1/;
    $refs{$_}=$odw;
    print "$_\n" if $debug_refs == 1;
    
    $_=$_."()";
    if (!defined($ref{$_}))
    {
      print "$_\n" if $debug_refs == 1;
      $refs{$_}=$odw;
    }
  }
  close(REFS);
}

sub dumprefs()
{
  $nr=0;
  foreach $func (%refs)
  {
    if ($nr == 1)
    {
      $nr=0;
      next;
    }
    $nr=1;
#    chop $func;
    print "$func -> $refs{$func}\n";
  }
#  print $refs{"Frame::Frame"}
}

sub funcid
{
  ($func)=@_;
  print "$func ->" if $debug_funcid == 1;
  $func=~s/=[^,)]+//g;
  $func=~s/INT/int/g;
  $func=~s/DREAL/double/g;
  $func=~s/FRAME/Frame/g;
  $func=~s/,[ ]*/, /g;
  $func=~s/([(,][^,)]*\W)\w+/$1/g;
  $func=~s/[ ]*([,)])/$1/g;
  $func=~s/\s+/ /g;
  $func=~s/inline\s+//g;
  $func=~s/virtual\s+//g;
  $func=~s/friend\s+//g;
  print "$func\n" if $debug_funcid == 1;
  return $func;
}

sub print_func_name
{
  ($_)=@_;
  print FILE "<li>";
  s/virtual\s+//;
  $x=$_;
  $s=$document{$x};
  $_=$funcname{$x};
  if ($s)
  {
    $s=~m/^(id[0-9]+)/;
    print FILE "<a href=#$1>";
    push(@needdoc, $x);
  }
  s/&/&amp;/g;
  s/</&lt;/g;
  s/>/&gt;/g;
  s/(.* )?(\S+)\(/$1<b>$2<\/b>\(/;
  print FILE "$_";
  print FILE "</a>" if $s;
  print FILE "<br>\n";
}

loadrefs();
dumprefs() if $debug_refs == 1;

if ($ARGV[0] eq "")
{
  print "Uzycie:";
  print "  $0 <nazwa_klasy>\n";
  exit(0);
}

$class = $ARGV[0];
print "--- Klasa $class ---\n";

foreach $file (@cfiles)
{
  print "$file\n";
  open(FILE, "<".$dir.$file);
  $stan = 0;
  $kom = 0;
  $inline = 0;
  $type="private";
  # pierwsze czytanie pliku - nazwy funkcji
  while (<FILE>)
  {
    # stan 0 - poza klasa
    # stan 2 - wewnatrz interesujacej nas klasy
    if ($kom == 1)
    {
      next unless m,\*/(.*),;
      $_=$1;
      $kom = 0;
    } else
    {
      if (m,^(.*)/\*,)
      {
        $kom = 1;
	$_ = $1;
      }
    }
    if ($inline == 1)
    {
      next unless m/}(.*)/;
      $_ = $1;
      $inline=0;
    }
    if ($stan == 1)
    {
      next unless /;/;
      s/^[^;]*;\s+//;
      $stan=0;
      print "***stan 1***";
    }
    if ($stan == 2)
    {
#      print ":_:$_:  :funcstring:$funcstring:\n";

      if (/{/)
      {
        if (/{.*}/)
	{
	  s/{.*}//;
	} else
	{
	  $inline = 1;
	  next;
	}
      }
      
      $_ = $funcstring." ".$_;
      s/\s+/ /g;
      if (m/(\w*):/)
      {
        print "***$1***\n" if $debug_nazwy == 1;
	$_="";
	$type="public" if $1 eq "public";
      }
#      print "---\n$_\n---\n";
      if (m/(.*)\)/)
      {
        $func=$1.")";
	$func=~s/^\s+//;
	$name=$func;
	$func=funcid($func);
	$funcname{$func}=$name;
	if ($debug_nazwy == 1)
	{
	  print "function: \"$func\" [$type]\n";
	  print "funcname: \"$name\"\n";
	}
	$_="";
	push(@privfunc, $func) if $type eq "private";
	push(@protfunc, $func) if $type eq "protected";
	push(@pubfunc, $func) if $type eq "public";
      }
      s/^[^;}{]*;//;
      
      if (/{/)
      {
#        print "***\n$funcstring\n***\n";
        if (/{.*}/)
	{
	  s/{.*}//;
	} else
	{
	  $inline = 1;
	  $funcstring="";
	  next;
	}
      }
      
#      print "~~~\n$funcstring\n~~~\n";
      $funcstring = $_;
      $stan=0 if m/}/;
    }
    next unless m/[a-zA-Z0-9]/;
    if (/^class/)
    {
      m/^class\s+([a-zA-Z0-9]+)/;
      $classname=$1;
      print "nazwa klasy: $1\n\n" if $debug_nazwy == 1;
#      push(@classes, $classname);
      next if /;/;                    # np. class Frame;
      while (! /{(.*)/) { $_=<FILE>; }
      $stan=2 if $classname eq $class;
      m/{(.*)/;
      $funcstring = $1;
    }
  }
  seek(FILE, 0, 0);
  $stan=0;
  $nrlin=0;
  
  # drugie czytanie pliku - znajdowanie komentarzy do funkcji
  while (<FILE>)
  {
    # stan 1 - wewnatrz komentarza /** */
    # stan 2 - po interesujacym komentarzy
    $nrlin++;
    if ( $stan == 2 )
    {
      chop;
      s/\s+/ /g;
    }
    s/begin/{/g if $stan==2;
    $linia="$linia"."$_" if $stan==1 or $stan==2;
    if ($stan == 2)
    {
#      print "*$linia*";
#      $linia=~s/\s+/ /g;
      if ($linia=~m/^(.*\S)\s*{/)
      {
        $linia=$1;
        $stan=0;
	$linia=~m/(\w+)::/;
	print "Klasa: \"$1\"\n" if $debug_kom == 1;
	if ($1 eq $class)
	{
	  $linia=~s/(\w+):://;
          $linia=funcid($linia);
	  print "Funkcja: \"$linia\"\n" if $debug_kom == 1;
	  $document{$linia}="id$nrlin\n".$doc;
	}
      } else
      {
         print ",$linia,\n" if $debug_kom == 1;
      }
    }
    if (m,/\*\*([^\*].*)$,)
    {
      $stan=1;
      if ($debug_kom == 1)
      {
        print "=====================\nKomantarz! (linia $nrlin)\n";
      }
      $linia="$1";
#      print "_____________________\n";
#      print "___ linia: $linia ___\n";
    }
    if ($stan==1 and $linia=~m,\*\/,)
    {
      $stan=0;
      $linia=~s/\*\/.*//;
      print "Koniec komentarza (linia $nrlin)\n" if $debug_kom == 1;
#      print "linia: $linia\n";
      if ($linia=~m/\@doc/)
      {
        $nazwfunk="";
	print "$linia" if $debug_dok == 1;
        if ($linia=~m/\@doc\<(.*)\>/)
	{
	  $nazwfunk=$1;
	  print "kom. do funk $nazwfunk\n" if $debug_nazwwk == 1;
	}
        $doc=$linia;
	$doc=~s/(.*)\@doc(\<.*\>)?//;
	$doc=~s/^\s+//g;
	$doc=~s/\r//g;
#	$doc=~s/\n[ \t]+/\n/g;
	$stan=2;
	if (!($nazwfunk eq ""))
	{
	  $stan=0;
	  if ($nazwfunk=~m/^(\w+)::(.*)/)
	  {
	    if ($1 eq $class)
	    {
	      print "Moja funkcja $2\n" if $debug_nazwwk == 1;
              $document{$2}="id$nrlin\n".$doc;	    
	    }
	  }
	}

	if ($debug_dok == 1)
	{
          print "Dokumantacja: \n";
	  print "$doc";
	}
	$linia="";
      } else
      {
        print "pusty komentarz /** */ (linia $nrlin)\n";
      }
    }
  }
  close(FILE);
#  print "@classes @pubfunc\n";
}

open(REFS, ">>refs.dat");
print REFS "$class\:\:\%top\n";
print REFS "$class.html\n";
open(FILE, ">$class.html");
print FILE "<HTML>\n";
print FILE "<TITLE>Class $class</TITLE>\n";
print FILE "<BODY bgcolor=#ffffff link=#0000ff vlink=#00007f text=#000000>\n\n";
print FILE "<H1>$class</H1>\n\n";
if (defined($document{"\%descr"}))
{
  print "Jest descr!\n" if $debug_descr == 1;
  print FILE "<a href=\"#descr\">description...</a><p>\n";
  push(@needdoc, "\%descr");
  $funcname{"\%descr"}="";
  $document{"\%descr"}=$document{"\%descr"}."<p><hr>\n";
}
print FILE "<H3>public:</H3>\n";
print FILE "<ul>\n";


foreach (@pubfunc)
{
  print_func_name($_);
}

foreach (@privfunc)
{
  print_func_name($_);
}

foreach (@protfunc)
{
  print_func_name($_);
}

print FILE "</ul>\n\n<hr>\n\n";

if (defined($document{"\%descr"}))
{
  print FILE "<a name=descr>\n<h2>Description:</h2>\n";
}

foreach (@needdoc)
{ 
  $funcid=$_;
  $doc=$document{$_};
  $_=$funcname{$_};
  s/=[^),]+//g;
  s/&/&amp;/g;
  s/</&lt;/g;
  s/>/&gt;/g;
  if (!($_ eq ""))
  {
    $doc=~s/^(id[0-9]+)/<a name=$1>\n<FONT size=4><b>$_<\/b><\/FONT><br>/;
    $refx=$1;
  } else
  {
    $doc=~s/^(id[0-9]+)/<a name=$1>\n/;
    $refx=$1;
  }
  print REFS "$class\:\:$funcid\n$class.html#$refx\n" unless $ENV{"doc_pl_refs"} eq "n";
  
#tlumaczenie @i(...)
  $doc=~s/\@i\(([^)]+)\)/<i>$1<\/i>/g;
  
#tlumaczenie @seealso
  if ($doc=~/\@seealso/)
  {
    print "Jest see also\n" if $debug_seealso == 1;
    $doc=~s/\@seealso\s+(\S+)/<p><FONT size=3><b>See also:<\/b><\/FONT><br>\n\@ref<$1>/;
    print "Param: $1\n" if $debug_seealso == 1;
    $doc=~s/\@seealso\s+(\S+)/<br>\n\@ref<$1>/;    
  }
  
#tlumaczenie @ref<...>
  while ($doc=~/\@ref<([^>]*)>(\(([^)]*)\))?/)
  {
    print "Jest ref: $1\n" if $debug_sub_refs == 1;
    if (defined($3) and $debug_sub_refs == 1)
    {
      print "Jest param: $3\n";
    }
    $ref=$refs{$1};
    if (!defined($ref))
    {
      $ref=$refs{"$class\:\:$1"};
      print "Szukam $class\:\:$1\n" if $debug_sub_refs == 1;
      if (!defined($ref))
      {
        print "nieznane odwolanie do $1\n" if $ENV{"doc_pl_refs"} eq "n";
	$ref=ERROR;
      }
    }
    $doc=~s/\@ref<([^>]*)>(\(([^)]*)\))?/<a href="$ref">MIEJSCE_NA_NAZWE_534532<\/a>/;
    if (defined($3))
    {
      $nazwa=$3;
    } else
    {
      $nazwa=$1;
    }
    $doc=~s/MIEJSCE_NA_NAZWE_534532/$nazwa/;
  }
  
#tlumaczenie @param
  if ($doc=~m/\@param/)
  {
    print "Jest param!!!!!" if $debug_gendok == 1;
    $doc=~s/\@param/<table>\@param/;
    $doc=~s,\@param\s+(\S+)\s+([^\@]+),<tr><td><i>$1</i></td><td>$2</td></tr>,g;
    if ($doc=~m/\@endparam/)
    {
      $doc=~s/\@endparam/<\/table>/;
    } else
    {
      $doc=$doc."</table>";
    }
  }
  print FILE "$doc<p>\n\n";
}

print FILE "</HTML>"