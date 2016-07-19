LoadPackage( "AutoDoc" );

AutoDoc( "itcp" : scaffold := true );

PrintTo( "VERSION", PackageInfo( "itcp" )[1].Version );

QUIT;
