main ( ) {
	type myinteger = short ;
	var foo , bar : void ;
	const FALSE = 0 ;
	const TRUE = 1 ;
	foo = 1 ;
	bar = 2 ;
	while ( foo != 10 ) {
		foo = foo + 1 ;
		bar = ( bar * foo ) / 2 ;
	}
	if ( bar > 100 ) {
		print 1 , 3 , 3 , 7 ;
	}
}