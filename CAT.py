# CAT Solver Sudoku Project
# CSC 320
# Jakob Roberts & Joe Czepil & Cole McGinn
#==============================================================================
import sys
from subprocess import call
#==============================================================================
def errorP():
	print "  ____                   "
	print " / __ \                  "
	print "| |  | | ___  _ __  ___  "
	print "| |  | |/ _ \|  _ \/ __| "
	print "| |__| | (_) | |_) \__ \ "
	print " \____/ \___/| .__/|___/ "
	print "             | |         "
	print "             |_|	        "
	print " SOMETHING BROKE!!!!!!!! "
#==============================================================================
def checkMiniSat():
	if call(['which','minisat'])==0:
		minisat = 'minisat'
		print "You are running << Minisat 1 >>"
	elif call(['which','minisat2']) ==0:
		minisat = 'minisat2'
		print "You are running << Minisat 2 >>"
	else:
		print "Ain't no minisat here!!"
		errorP()
		return
#==============================================================================
def doMiniSat(input):
	checkMiniSat()

	print "test"



#==============================================================================
def getdemacs(inlines):
	xaxis = 1
	yaxis = 1
	count = 0
	dimacs = []
	puzzle = inlines[0]
	while(xaxis < 10):
		dimnum = ((81*(int(float(xaxis)) - 1)) + (9*(int(float(yaxis)) - 1)) + ((int(float(puzzle[count]))) + 1))
		dimacs.append(dimnum)
		yaxis += 1
		if(yaxis == 10):
			xaxis += 1
			yaxis = 1
		print("%d\n"% dimacs[count])
		count += 1

	return dimacs


#==============================================================================
def main():
	#-- INPUT CHECK
	canread = False
	try:			# check if can open file
		infile = open(sys.argv[1],'r')
		canread = True
	except IndexError: 	# read from stdin if no file
		infile = sys.stdin
		canread = True
	except IOError:		#file doesn't exist so print error!
		print("File specified does not exist!")

	#-- PARSE FILE/INPUT
	if canread:
		with infile:
			thelines = infile.readlines()

		ret = getdemacs(thelines)



#==============================================================================
if __name__ == "__main__":
	main()
