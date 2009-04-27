Here are a few things that you should keep in mind when implementing Project 4:


1) When printing the Symbol Table entries or the errors, make sure to conform to the format shown in the test*.out files.
    
2) When printing the Symbol Table entries, make sure to indent depending on the current nesting level, e.g.: 
	N: sym1 C: PROCEDURE T: void
	-->N: newType C: TYPE T: int 
	-->N: newType2 C: TYPE T: array 10 of newType 

3) If you are using the Parser file provided for Project 3, you NEED TO UNCOMMENT the code enclosed in the following block comment : "/**DO NOT UNCOMMENT*/".

4) Make sure to use the printError(int, int) method when you want to print errors.

