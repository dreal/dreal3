#!/usr/bin/env python
import os
import time

RESULT_DIR="./result"
FORMULA_DIR="./flyspeck_ineqs"

def firstLine(filename):
        '''Print a file to the standard output.'''
	f = file(filename)
        return f.readline().rstrip()

def print_header():
        print "<div id=\"demo\">"
        print "<table cellpadding=\"0\" cellspacing=\"0\" border=\"0\"",
        print "class=\"display\" id=\"example\">"
        print "<thead>"
        print "<tr>"
        print "<th>Filename</th>"
        print "<th>Formula ID</th>"
        print "<th>Result</th>"
        print "<th>Complexity1</th>"
        print "<th>Complexity2</th>"
        print "<th>Elapsed Time</th>"
        print "<th>DateTime</th>"
        print "</tr>"
        print "</thead>"
        print "<tbody>"
        
def print_footer():
        print "</tbody>"
        print "<tfoot>"
        print "<tr>"
        print "<th>Filename</th>"
        print "<th>Formula ID</th>"
        print "<th>Result</th>"
        print "<th>Elapsed Time</th>"
        print "<th>DateTime</th>"
        print "</tr>"
        print "</tfoot>"
        print "</table>"
        print "</div>"

print_header()

drFiles = [x[:-4] for x in os.listdir(RESULT_DIR) if x.endswith("out") ]
for dr in drFiles:
    mtime_sec = os.stat(RESULT_DIR + "/" + dr + ".out").st_mtime
    mtime_str = time.strftime("%a, %d %b %Y %H:%M:%S", time.localtime(mtime_sec))
    drPathName = FORMULA_DIR + "/" + dr
    outPathName = RESULT_DIR + "/" + dr + ".out"
    resultPathName = RESULT_DIR + "/" + dr + ".result"
    result_str = firstLine(resultPathName)
    time_str = firstLine(RESULT_DIR + "/" + dr + ".time")
    ID_str = firstLine(RESULT_DIR + "/" + dr + ".ID")

    if result_str[0:3] == "sat":
            result_str = "SAT"
            class_str = "gradeA"
    elif result_str[0:3] == "uns":
            result_str = "UNSAT"
            class_str = "gradeC"
    else:
            result_str = "FAIL"
            class_str = "gradeX"

    print "<tr class=\"" + class_str + "\">"
    print "<td align='center'><a href=\"" + drPathName + "\">",
    print dr + "</a></td>",
    print "<td align='left'>" + ID_str + "</td>"
    print "<td align='center'><a href=\"" + outPathName + "\">",
    print result_str + "</a></td>"
    print "<td align='center'>" + time_str + "</td>"
    print "<td align='center'>" + mtime_str + "</td>"
    print "</tr>"

print_footer()
