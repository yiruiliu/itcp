################################################################################
##
##                                                                 itcp package
##
##  Copyright 2016,                                                Jayant Apte
##                                                                 John Walsh
##
##  The .gd file containing global function declarations and the documentation
##  of the itcp package. The documentation is created using the AutoDoc Package.
##
##
#############################################################################



#! @Chapter Introduction
#! ITCP stands for Information Theoretic Converse Prover. Several converse proofs, like those arising in
#! multi-source network coding over directed acyclic hypergraphs, distributed storage, secret sharing, and graph guessing games etc.,
#! can be divided into two parts: 1) What to prove? 2) How to prove? ITCP is a software that allows
#! one to use a computer to generate sensible statements of converse proofs i.e. part 1). The actual proof, i.e. part 2), can
#! then be generated using Yeung's framework <Cite Key="yeunginfoframework"/> and linear programming duality (see eg. <Cite Key="lihmsnc"/>, <Cite Key="TianJSAC433"/>). Currently, it supports the following types of converse proofs:
#! * Polyhedral Converse (Network Coding): Given a multi-source network coding instance, determine the tightest
#!   set of inequalities amoungst source rate and edge capacity variables that
#!   are implied by Shannon-type and (if specified) given non-Shannnon-type information
#!   inequalities
#! * Sum-rate Converse (Network Coding): Given a multi-source network coding instance, determine
#!   the least upper bound on the sum of source rates, implied by Shannon-type and (if specified) given non-Shannnon-type information
#!   inequalities, under specified edge capacities.
#! * Worst-case information ratio lower bounds (Secret Sharing): Given an access structure, determine the greatest
#!   lower bound on the workst case information ratio implied by Shannon-type and (if specified) given non-Shannnon-type information
#!   inequalities
#! * Guessing Number upper bounds (Guessing Games played on directed graphs): Given a directed graph, determine the
#!   least upper bound on its guessing number implied by Shannon-type and (if specified) given non-Shannnon-type information
#!   inequalities
#! The last three types of converse proofs can be performed by using linear programming techniques. This involves solving a linear program,
#! whose optimum value gives us an upper (lower) bound. Then, one uses dual optimal vertex to provide a human readable proof that tells us how to
#! combine various information inequalities to arrive at the aforementioned upper (lower) bound. For the first type of converse proof, however,
#! one requires more sophisticated tools. For that purpose, ITCP uses polyhedral projection algorithm symchm, implemented in another GAP package that goes by The
#! same name. In all of the problems mentioned above, one has to either project or solve linear programs over polytopes that have exponentially many dimensions
#! compared to the problem size. A key feature of ITCP is automatic detection of problem symmetries and symmetry exploitation to reduce the ComplexityOfAlgebra
#! of solving the above problems, so that one can approach ever larger problems from a computational perspective.
#! @Chapter Installation
#! ITCP requires GAP package symchm <Cite Key="jayantsymchm"/> for symmetry exploiting polyhedral projection, along with
#! package $\texttt{qsopt}\_\texttt{ex-interface}$ for solving linear programs exactly using rational arithmetic.
#! You can find information about how to install them in their respective user manuals.
#! To get the newest version of ITCP, download the .zip archive from <URL>https://github.com/jayant91089/itcp</URL>
#! and unpack it using
#! $$\texttt{unzip itcp-x.zip}$$
#! Do this preferably inside the $pkg$ subdirectory
#! of your GAP 4 installation. It creates a subdirectory called $itcp$.
#! This completes the installation of the package. If you do not know the whereabouts of the $pkg$ subdirectory, invoke the following in GAP:
#! @BeginCode pkg
GAPInfo.("RootPaths");
 #! @EndCode
#! @InsertCode pkg
#! Look for pkg directory inside any of the paths returned.
#! One can then start using ITCP by invoking
#! @BeginCode Read
 LoadPackage( "itcp");
 #! @EndCode
#! $$gap>$$
#! @InsertCode Read
#! from within GAP. This would automatically load the dependencies $symchm$ and $\texttt{qsopt}\_\texttt{ex-interface}$, so you don't have to load them seperately.
#! @BeginCode GF
q:=4;;
F:= GF(q);; # here q must be a prime power
#! @EndCode

#! @Chapter Usage
#! @Section Available functions
#!  In this section we shall look at the functions provided by ITCP.
#! @Description
#!  This function finds the Network Symmetry Group of the input network instance
#! bounding the rate region of an instance of mult-source network coding on directed acyclic hypergraphs.
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! Returns a subgroup of symmetric group of $nvars$ labels
#! @Returns A group
#! @Arguments ncinstance
DeclareGlobalFunction("NetSymGroup");
#! $\textbf{NOTE 1:}$ Certain naming convensions are followed while defining network coding instances. The source messages are labeled with
#! $[1...nsrc]$ while rest of the messages are labeled $[nsrc...nvars]$. Furthermore, the list $cons$ includes
#! all network constraints except source independence. This constraint is implied with the labeling i.e. ITAP
#! enforces it  by default for the messages labeled $[1...nsrc]$.
#! @Description
#!  This function finds the minimal (non-redundant) collection of inequalities
#! bounding the rate region of an instance of mult-source network coding on directed acyclic hypergraphs.
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! * $usesym$ is a boolean indicating whether symmetry should be used in computation
#! * $optargs$ is a list of optional arguments $[nsrec,..]$ where $nsrec$, when specified, is a GAP record that specifies
#!   any non-Shannon type information inequalities to be included in the computation.
#! Returns a list $[rr,rrstring]$ where $rr$ is a list of normal vectors of the inequalities bounding the rate region,
#! that are inequivalent under the Network Symmetry Group of $ncinstance$ if $usesym$ is true, otherwise $rr$ contains
#! all such normal vectors, under assumption of no symmetries.
#! $rrstring$ is a string that can be used to display inequalities associated with $rr$ in an easier to read format.
#! @Returns A list
#! @Arguments ncinstance,usesym,optargs
DeclareGlobalFunction("NCRateRegionOB");
#! $\textbf{NOTE 2:}$ Currently ITCP supports specifiation of non-Shannon ineqality of Zhang and Yeung <Cite Key="zyineq97"/> and 214 new
#! non-Shannon inequalities found by Dougherty, Freiling and Zeger <Cite Key="dfznonshannon"/>. These inequalities can be applied to any collection
#! of 4 subsets of a given set of random variables. The keys of the record $nsrec$ can be integers $1,...,215$ where index $1$ corresponds to the ZY inequality
#! while $2,...,215$ correspond to the inequalities found by Dougherty, Freiling and Zeger. The value associated wth each key is a list of 4-subsets
#! of subsets of $nvars$ random variables associated with the network. Internally, several permuted forms of these inequalities are created, so as to not
#! break the symmetries of the network coding instance, that are exploited during the computation.
#! @Description
#!  This function finds least upper bound on the sum of all source rates that is implied
#! by the Shannon-type and (if specified) the non-Shannon-type inequalities.
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! * $caps$ is a list of $nvars-nsrc$ non-negative integers, specifying the capacity of the edges
#! * $optargs$ is a list of optional arguments $[nsrec,..]$ where $nsrec$, when specified, is a GAP record that specifies
#!   any non-Shannon type information inequalities to be included in the computation (see NOTE 2 for explanation of the format).
#! Returns a rational number specifying the upper bound
#! @Returns A rational number
#! @Arguments ncinstance,caps,optargs
DeclareGlobalFunction("NCSumRateUB");

#! @Description
#!  This function finds the greatest lower bound on the worst case information ratio of a secret sharing instance.
#! * $Asets$ - A list of authorized sets each specified as a subset of $[nvars-1]$
#! * $nvars$ - Number of participants (including one dealer)
#! * $optargs$ is a list of optional arguments $[nsrec,..]$ where $nsrec$, when specified, is a GAP record that specifies
#! any non-Shannon type information inequalities to be included in the computation (see NOTE 2 for explanation of the format).
#! Returns a rational number
#! @Returns A rational number specifying the lower bound
#! @Arguments Asets,nvars,optargs
DeclareGlobalFunction("SSWorstInfoRatioLB");

#! $\textbf{NOTE 3:}$ No input checking is performed to verify if input $Asets$ follows labeling convensions.
#! @Description
#!  This function finds the least upper bound on the guessing number of a directed graph.
#! * $G$ - A list with 2 elements: 1) a list of vertices 2) a GAP record each vertex of the graph to a a list neighbors with edges incoming to it
#! * $optargs$ is a list of optional arguments $[nsrec,..]$ where $nsrec$, when specified, is a GAP record that specifies
#! any non-Shannon type information inequalities to be included in the computation (see NOTE 2 for explanation of the format).
#! Returns A rational number
#! @Returns A rational number specifying the upper bound
#! @Arguments Asets,nvars,optargs
DeclareGlobalFunction("GGnumberUB");

#! $\textbf{NOTE 4:}$ Certain naming convensions are followed while graph $G$. The vertices are labeled by the set $\{1,...,n\}$ where
#! $n$ is the number of vertices of the graph. Hence, the keys of the record $G$ are integers $\{1,...,n\}$. The value for a key $t$ is a list
#! $[i,j,...]$ where $i,j,...$ are verties s.t. $(i,t),(j,t),...$ are the directed edges of the graph.
