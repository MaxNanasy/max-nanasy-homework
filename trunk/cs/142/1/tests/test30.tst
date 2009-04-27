const MAX = 12;	
type t = int; 
type t1 = array 12 of t;

void theProcedure( ) {
   var x, y, z : t1;
   var i : int;
   int testProc() {
	return i * i;	
   }	

   i = 0;
   while (i < MAX) {
	x[i] = ::testProc();
   }
}
main() {
   ::theProcedure();
}