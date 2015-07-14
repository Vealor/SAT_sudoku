# CAT Solver Sudoku Project
# CSC 320
# Jakob Roberts & Joe Czepil & Cole McGinn
#==============================================================================
import sys
#==============================================================================
def theSolver(inlines):
	print inlines

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
		ret = thesolver(thelines)

#==============================================================================
if __name__ == "__main__":
	main()
