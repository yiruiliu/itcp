Instructions for building ITCP documentation:
1) Go to itcp folder inside GAP pkg directory and start gap (either local or global GAP)
2) gap> LoadPackage("itcp");
3) gap> LoadPackage("AutoDoc");
4) gap> Read("<path to itcp folder>/doc/itcp_buildman.g"); # contains functions for building documentation
4) gap> path:="/home/aspitrg3-users/jayant/gap_install/gap4r7/pkg/itcp/"
5) gap> buildman(path);

________________________________________________________________________________________________________

NOTE 1: Function buildman above constructs the manual using AutoDoc as follows:
1) Merge in-code documentation itcp.gd and examples in doc/examples.txt to create new itcp.gi file1
2) Running gap> AutoDoc("itcp":autodoc:=true);
3) Unmerging examples to restore itcp.gi

NOTE 2: examples.txt contains examples in Autodoc format. They appear in the same order as the associated functions in
itcp.gd (it is important to maintain this order). For buildman() to associate the examples with respective functions
add "#!##<funcname>" tag before @BeginExample, when creating new examples.
