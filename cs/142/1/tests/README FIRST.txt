RUNNING THE TEST SCRIPT
: wintestall.bat (for windows)
: unixtestall.sh (for unix)

This is the test script that we will be using to test your program. 
The number of points lost by students who relied only upon what they 
could "see" to be a correct comparison are enormous. Even when we
have provided a script to prevent this. Please, don't make the same 
mistake when it is really unnecessary (and very costly in terms of 
points-- TRUST ME, THIS IS NOT THE ASSIGNMENT THAT YOU WANT TO DROP).

WHAT DOES IT DO?
1) compiles your files
2) runs your program with a given input file, and compares them
   to the expected output using the file compare (fc) command.

WHAT SHOULD YOU SEE?
You will see the a message written to the screen indicating which
test is being run. Following the "fc" command, you should ideally
see nothing. If you do see something, the "fc" command is trying to
tell you where your output differs from ours. Please take the time
to figure out the results. The results it displays begin with the
first differences encountered by the output of your file & the
reference file.

TO RUN THE TEST SCRIPT:

You need to run it from the MS-DOS command prompt. To do this:

1) Click Start->Run. Type Cmd at the "Open:" prompt.

2) At the DOS prompt, change to your test directory
(home of your testall.bat file).

To do this, use the following sequences of commands:

dir :this command shows you what is in the current directory
cd  :the "cd" command allows you to change to directories.
      Note: "cd .." will take you down one directory

3) Type "testall" at the command prompt.

(NOTE: Unix users need to open a terminal on a Unix machine, change to
the directory of the test script, and run it from there.)