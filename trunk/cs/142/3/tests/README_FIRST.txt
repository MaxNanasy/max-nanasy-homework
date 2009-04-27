Here are a few things that you should keep in mind when implementing Project 3:

1) When printing the Symbol Table entries, make sure to conform to the following format: "N: <name> C: <classification> T: <type> V: <value>", e.g.: 
	N: int C: TYPE T: null
	N: newType C: TYPE T: int 
	N: sym1 C: PROCEDURE T: void
   If the particular symbol has no value (e.g. types), don't print the "V: <value>" section.
   For arrays, don't print "V: <value>" and instead print "D: <dimension>"
    
2) When printing the Symbol Table entries, make sure to indent depending on the current nesting level, e.g.: 
	N: sym1 C: PROCEDURE T: void
	-->N: newType C: TYPE T: int 
	-->N: newType2 C: TYPE T: newType D: 10

3) In the provided Parser file, do NOT uncomment code enclosed in the following block comment : "/**DO NOT UNCOMMENT*/".

4) Make sure to use the printError(int, int) method when you want to print errors.

5) Constants are always assumed to be of type short.
