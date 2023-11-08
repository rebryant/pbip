#!/usr/bin/python3

import sys
import datetime
import getopt

import pbip

def usage(name):
    print("Usage %s: [-h] [-v VERB] [-b] [-S] [-R] -i FILE.cnf -p FILE.pbip [-o FILE.lrat]")
    print("  -h           Print this message")
    print("  -v VERB      Set verbosity level")
    print("  -b           Pure BDD mode.  Don't make use of clausal representations")
    print("  -S           Disable SDP processing of CNF")
    print("  -R           Don't reorder variables")
    print("  -i FILE.cnf  Input CNF file")
    print("  -p FILE.pbip Input proof file")
    print("  -o FILE.lrat Output proof file")


def run(name, argList):
    verbLevel = 1
    cnfName = ""
    pbipName = ""
    lratName = ""
    bddOnly = False
    reorder = True
    sdpReduce = True

    optlist, args = getopt.getopt(argList, "hbRSv:i:p:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-b':
            bddOnly = True
        elif opt == '-R':
            reorder = False
        elif opt == '-S':
            sdpReduce = False
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            pbipName = val
        elif opt == '-o':
            lratName = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if cnfName == "":
        print("ERROR: Must give name of CNF file")
        usage(name)
        return
    if pbipName == "":
        print("ERROR: Must give name of PBIP file")
        usage(name)
        return
    start = datetime.datetime.now()
    pb = pbip.Pbip(cnfName, pbipName, lratName, verbLevel, bddOnly, reorder, sdpReduce)
    pb.run()
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        print("PBIP: LRAT generation elapsed seconds: %.2f" % (seconds))


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
