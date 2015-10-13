                 ======================================
                 ====== T2 TEMPORAL LOGIC PROVER ======
                 ======================================

In this directory you will find the sources for the T2 temporal logic prover.
T2 is designed to prove temporal properties of programs, such as safety,
termination, or properties specified in the logic CTL.
In this document, we first discuss how to use the tool and explain how to build
it. Then, we give a rough overview of the implementation, and finally list the
developers of the tool and point to some related research papers.

                              -----------
                              Building T2
                              -----------
Windows
~~~~~~~
To build T2, we recommend using Visual Studio (2013 or later), but you can
also follow the Mono instructions provided below. In Visual Studio, the used
NuGet packages are managed through Visual Studio and do not need to be
downloaded manually (i.e., skip step (4)).
To use the included libz3.dll, you need to install the Visual Studio 2015
C++ run-time from
  https://www.microsoft.com/en-us/download/details.aspx?id=48145

Using Mono (for Linux and MacOS)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To build T2, you will first need to build the .NET bindings of z3/spacer
using mono. For this, you need to get z3 sources from the "spacer-t2" branch
of https://bitbucket.org/spacer/code (cf. step (1)).

To install some needed .NET libraries, you will need NuGet, which you can
obtain from http://nuget.org/nuget.exe.

Let $NUGET be the path to your nuget.exe download, $Z3DIR the directory in
which you want to store your Z3 sources, and $T2DIR the directory in which
you want to store the T2 sources. You can set these environment variables
by "export NUGET=/path/to/nuget.exe" in your shell. Then follow these
steps:

(0) Install software needed for the build process, get T2 sources:
     * g++
     * python
     * mono for .NET 4.0
     * xbuild
     * fsharp

    On a Debian (>> squeezy) or Ubuntu (>= 14.04 LTS) system, this suffices:
      $ sudo apt-get install build-essential python mono-complete mono-xbuild fsharp

    On OS X, install the Mono MDK for Mac OS from
       http://www.mono-project.com/download/
    and install the XCode development tools (e.g., by executing "gcc" in
    a Terminal -- if it's not there yet, OS X will offer to install XCode).

    To download the T2 sources:
      $ mkdir -p "$T2DIR"
      $ git clone https://github.com/mmjb/T2.git
      $ export T2DIR="$T2DIR/T2"

(1) Build z3.
    On Linux, the following recipe retrieves the z3 sources and builds z3:
      $ mkdir -p "$Z3DIR"
      $ pushd "$Z3DIR"
      $ git clone https://bitbucket.org/spacer/code
      $ cd code
      $ git checkout spacer-t2
      $ ./configure
      $ cd build
      $ make
      $ popd

    On OS X, you need to enforce a 32bit build (for compatibility with Mono):
      $ mkdir -p "$Z3DIR"
      $ pushd "$Z3DIR"
      $ git clone https://bitbucket.org/spacer/code
      $ cd code
      $ git checkout spacer-t2
      $ ./configure
      $ cd build
      $ perl -i -pe 's/-D_AMD64_/-arch i386/; s/LINK_EXTRA_FLAGS=/$&-arch i386 /' config.mk
      $ make
      $ popd

(2) Build the .NET bindings for z3:
      $ pushd "$Z3DIR/code/src/api/dotnet/"
      $ xbuild Microsoft.Z3.csproj
      $ popd

(3) Update z3 and its .NET bindings in the T2 source tree:
      $ cp "$Z3DIR/src/api/dotnet/obj/Debug/Microsoft.Z3.*" "$T2DIR/src/"
      $ cp "$Z3DIR/build/libz3.*" "$T2DIR/src/"

(4) Get required packages via NuGet (may need to import certificates first):
      $ mozroots --import --sync
      $ pushd "$T2DIR/src" && mono $NUGET restore && popd

(5) Build T2, in Debug mode:
      $ pushd "$T2DIR/src" && xbuild && popd
    In Release configuration:
      $ pushd "$T2DIR/src" && xbuild /property:Configuration=Release && popd

(6) Run T2 as follows (replace "Debug" by "Release" for the release build)
      $ mono "$T2DIR/src/bin/Debug/T2.exe"
    For example, to execute the testsuite:
      $ pushd "$T2DIR/test" && mono "$T2DIR/src/bin/Debug/T2.exe" -tests


                                ----------
                                Running T2
                                ----------
T2 is run from the command line, and the following command line arguments are
used to define the proof goal:
 -input_t2 <string>:
    Path of the input file in T2 syntax. For examples, look at test/*.t2.

 -termination:
    Try to prove (non)termination.

 -safety <int>:
    Try to prove non-reachability of location <int>.

 -ctl <CTL_Formula>:
    Try to prove that <CTL_Formula> holds for the program.
    The formula format is as follows:
      - Path and temporal quantifiers are enclosed in square brackets,
        e.g. [AG], [EF], and [AW].
      - Subformulas following quantifiers have to be enclosed in
        parentheses, e.g. [AG](x > 0) and [EF]([AG](y < x)).
    For more CTL formula examples, see programTests.fs, or the parser
    definition in absparse.fsy.

 -ctlstar <CTLStar_Formula>:
    Try to prove that <CTLStar_Formula> holds for the program.
    The formula format is as follows:
      - E F(G ((tt > 0) || (A F (wakend == 0)) ))
      - One Path and one temporal quantifier can be paired at a time,
	separated by a space, followed by parantheses e.g. 
	E F(x == 0), E F(G (tt > 0)), and A F(G (E F (x == 0)))  .
      - Subformulas following quantifiers have to be enclosed in
        parentheses, as shown above.
    For more CTL formula examples, see programTests.fs, or the parser
    definition in absparse.fsy.

 -fairness <Fairness_Condition>:
    Try to prove termination/a CTL formula under <Fairness_Condition>.
    The format of <Fairness_Condition> is "(<P>, <Q>)", where a
    computation is unfair if an infinite number of states in it
    satisfy <P>, whereas <Q> is only satisfied finitely often.
    An example is "(P == 1, Q == 1)", and more examples can be
    found in programTests.fs.

Commonly used options that modify T2 output behaviour:
 -timeout <int>:
    Set timeout (in seconds).

 -print_proof:
    Print an explanation of the result (for termination only).

 -log:
    Turn on verbose logging. This will print a lot of output, and may
    be hard to understand for non-developers.

Typical calls of T2 on Windows, with output, look like this:
 $ src/bin/Debug/T2.exe -input_t2 test/testsuite/small02.t2 -safety 10000 -timeout 42
 Safety proof succeeded

 $ src/bin/Debug/T2.exe -input_t2 test/testsuite/small01.t2 -termination -print_proof
 Termination proof succeeded
 Used the following cutpoint-specific lexicographic rank functions:
   * For cutpoint 7, used the following rank functions/bounds (in descending priority order):
     - RF x, bound 2

 $ src/bin/Debug/T2.exe -input_t2 test/testsuite/heidy1.t2 -CTL "[AG] (x_1 >= y_1)"
 Temporal proof succeeded

 $ src/bin/Debug/T2.exe -input_t2 test/bakery.t2 -CTL "[AG](NONCRITICAL <= 0 || ([AF](CRITICAL > 0)))" -fairness "(P == 1, Q == 1)"
 Temporal proof succeeded

Note that T2 creates "defect" files when proofs fail and logging is enabled.
A defect.tt file can be viewed with sdvdefect.exe (which comes with the SDV
distribution).

                             -------------
                             Developing T2
                             -------------

In the following, we discuss several parts of the implementation in slightly
more detail, explaining how high-level algorithms (from our papers) are
implemented in T2.


Basics, glue and tests:
~~~~~~~~~~~~~~~~~~~~~~~

Implementation:
  * main.fs:
    Top level file for T2 program prover.
  * programTests.fs, test/*:
    The implementation of the T2 testsuite and oru example collection.
  * arguments.fs:
    Command-line arguments to the tool, and place where we store parameters.
  * log.fs:
    Central mechanism for controlling logging.
  * utils.fs, gensym.fs:
    Helper functions, and local extensions of existing F# data structures.
  * absflex.fsl, absparse.fsy, parseError.fs:
    F# Lexer/Yacc files for parsing T2 files.
  * z.fs:
    F# functions connecting to the Z3 decision procedure.


Representation of programs
~~~~~~~~~~~~~~~~~~~~~~~~~~

We use a very simple representation of programs, using control-flow graphs
annotated with "assume" and "assign" commands expressed in linear arithmetic
over integers.
Recursion, procedures, concurrency, heap, non-linearity are unsupported.
To deal with more complex programs we use tools such as SLAyer [8] or Thor
[17], which can be used to produce arithmetic abstractions of programs useful
for proving termination. In the literature we know how to deal with
recursion/procedures (e.g. [10]), concurrency (e.g. [10]), and non-linear
arithmetic (e.g. [16]) but these features are not implemented here in T2.

Implementation:
 * programs.fs:
   Simple representation for arithmetic, non-recursive programs.
 * counterexample.fs:
   Routines for dealing with counterexamples, which are sequences of program
   commands.
 * analysis.fs:
   Various standard compiler-level program analysis tools (e.g. live variable
   analysis).
 * var.fs:
   Representation of program variables.
 * input.fs:
   Interface for loading representations of programs into the tool.
 * output.fs:
   Collection of methods to output (intermediate) programs in other formats.
 * term.fs:
   Datatype representing terms.
 * formula.fs, relation.fs, sparselinear.fs:
   Datatypes representing linear formulae and relations. Many computations are
   implemented on a sparse representation of terms based on a map from variables
   to corresponding coefficients. Often, this is confused with a linear
   inequation, where the term is meant to be smaller or equal to 0.
   So for example, "2*x <= 4*y" is represented as a map m with m.[x] = 2,
   m.[y] = -4.
 * dominators.fs, scc.fs:
   Dominators computation using the technique from [33], strongly connected
   components computation.


Termination proving algorithm
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here the tool implements the TERMINATOR-based approach to termination proving
(e.g. [6,22,23]) with some modifications as described in [1] and [3]. For those
not well versed in formal methods literature the best place to start might be
by reading [6].  The idea of the technique is is to reduce the checking of
termination arguments to an incrementally evolving safety problem.  The
refinement of the current termination argument is performed on counterexamples
from the safety prover, which give rise to a form of lasso-counterexample.
T2 implements the optimizations/extensions/modifications from [1,3], which
modify the original technique to search for lexicographic termination
arguments as well as adapt techniques from the dependency-pairs approach to
termination proving.

Implementation:
 * termination.fs:
   Contains the main termination proving loop in the function "prover",
   as described in the original refinement-based termination papers [6,22,23].
   It also incorporates the optimizations for lexicographic termination proofs
   in this setting, as described in [1,3].
 * lasso.fs:
   Implements the subprocedures needed to analyze counterexample lassos to
   refine termination arguments, as discussed in [1,3,22,23].
 * instrumentation.fs:
   Provides the program modification procedures needed for refinement-based
   termination analysis.
   The initial transformation is performed by "instrument_F" (F ~ finally),
   and subsequent modification steps (for changed termination arguments)
   are in the instrument_*_RF and switch_to_* functions.
 * rankfunction.fs:
   Implements the actual rank function synthesis algorithms (based on Farkas'
   Lemma) presented in [24,25,26,27].
 * recurrentsets.fs:
   Rudimentary non-termination proving techniques based on [36], adapated to
   the lasso-setting.


Temporal Logic (CTL) proving algorithm
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This version of T2 incorporates the branching-time logic verifier described
in [34]. For those unfamiliar with temporal logic verification for
infinite-state systems, do refer to [7], where a technique that reduces
temporal property verification to a program analysis problem is described.
In this CTL model checker for infinite-state programs, we adapt the well-known
bottom-up strategy for finite-state CTL model checking [35] to infinite-state
programs using precondition synthesis. We leverage techniques for proving
safety, termination, and nontermination of programs to synthesize preconditions
asserting the satisfaction of CTL sub-formulae of an input property, and then
use the preconditions in the remaining proof. Thus, our implementation does not
need to consider the case of nested temporal quantifiers explicitly.

Implementation:
 * termination.fs:
   The main loop in the function "bottomUp" drives the proof process.
   It starts by initializing the map of preconditions and then calling itself
   recursively for each CTL sub-formula. The procedure "prover" is then used to
   return counterexamples to the sub-formulas, which are used to synthesize
   preconditions. Several preconditions for each program location can then be
   computed simultaneously. This procedure also propagates found pre-conditions
   throughout the graph, without recomputing them explicitly, as described in
   [34].
 * instrumentation.fs:
   Implements the reduction of model checking to safety checking and
   well-foundedness in the procedures "instrument_(X|F|G|...)", driven by the
   procedure "mergeProgramAndProperty".


Safety/reachability prover
~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we use McMillan's "lazy abstraction with interpolation" technique to
prove safety (aka reachability).  In our primary application of proving
termination the safety problems are encodings of the validity of termination
arguments.  Our version is incremental, as the termination proof search builds
a reachability problem and then, based on counterexamples found, refines the
reachability problem and re-checks it.

Implementation:
 * reachability.fs:
   Interpolation-based safety/reachability prover following the strategy of [28].
 * priostack.fs:
   Priority stack implementation used in safety prover.
 * interpolantSequence.fs:
   Farkas Lemma-based interpolant synthesis via Farkas lemma using an extension
   of the techniques from [29].
 * symex.fs:
   Symbolic execution used in lazy abstraction procedure


Abstract interpretation
~~~~~~~~~~~~~~~~~~~~~~~
We use several abstract interpretation techniques [31]. Of particular
importance is the use of an Octagon-based [30] abstract interpreter during
the analysis of lassos.

Implementation:
 * IIntAbsDom.fs:
   Interface for abstract domains (i.e. [31]).
 * IntervalIntDomain.fs:
   Intervals domain. See [32].
 * octagon2.fs:
   Octagon domain. See [30].


                                 ------
                                 People
                                 ------
The following people have contributed to this version of T2:

* Josh Berdine (MSR Researcher)
* Mary Boeker (12 week undergraduate intern, Queen Mary University of London)
* Marc Brockschmidt (MSR Researcher)
* Hongyi Chen (12 week PhD intern, Lousiana State University)
* Nathan Chong (12 week PhD intern, Imperial College)
* Byron Cook (MSR Researcher, University College London)
* Ruslan Ledesma Garza (12 week PhD intern, Technical University Munich)
* Mihaela Gheorghiu (12 week PhD intern, University of Toronto)
* Samin Ishtiaq (MSR Researcher)
* Heidy Khlaaf (PhD Contractor, University College London)
* Zachary Kincaid (12 week PhD intern, University of Toronto)
* Matt Lewis (12 week PhD intern, Oxford)
* Abigail See (12 week Undergraduate intern, Cambridge University)
* Vlad Shcherbina (12 week PhD intern, Moscow State University)
* Christoph Wintersteiger (MSR Researcher)




                               ----------
                               References
                               ----------


[1] Better termination proving through cooperation
    Marc Brockschmidt, Byron Cook, Carsten Fuhs
    CAV 2013

[2] Reasoning about nondeterminism in programs
    Byron Cook and Eric Koskinen
    PLDI 2013

[3] Ramsey vs. lexicographic termination proving
    Byron Cook, Abigail See, and Florian Zuleger
    TACAS 2013

[4] Temporal property verification as a program analysis task (extended version
    Byron Cook, Eric Koskinen, Moshe Vardi
    Formal Methods in System Design (special issue from CAV), 2012

[5] Proving termination of nonlinear command sequences
    Domagoj Babic, Byron Cook, Alan J. Hu, Zvonimir Rakamaric
    Formal Aspects of Computing (special issue from SEFM), 2012

[6] Proving program termination (Review article)
    Byron Cook, Andreas Podelski, Andrey Rybalchenko
    Communications of the ACM, Volume 54 Issue 5, May 2011

[7] Temporal property verification as a program analysis task
    Byron Cook, Eric Koskinen, Moshe Vardi
    CAV 2011

[8] SLAyer: Memory safety for systems-level code
    Josh Berdine, Byron Cook, Samin Ishtiaq
    CAV 2011

[9] Making prophecies with decision predicates
    Byron Cook and Eric Koskinen
    POPL 2011

[10] Summarization for termination: No return!
     Byron Cook, Andreas Podelski, Andrey Rybalchenko
     FMSD (2009) 35:369-387

[11] Proving that non-blocking algorithms don't block
     Alexey Gotsman, Byron Cook, Matthew Parkinson, and Viktor Vafeiadis
     POPL 2009

[12] Principles of program termination
     Byron Cook
     Notes from the 2008 Marktoberdorf summer school

[13] Proving conditional termination
     Byron Cook et al
     CAV 2008

[14] Ranking abstractions
     Aziem Chawdhary et al
     ESOP 2008

[15] Proving thread termination
     Byron Cook, Andreas Podelski, and Andrey Rybalchenko
     PLDI 2007

[16] Proving termination by divergence
     Domagoj Babic, Byron Cook, Alan Hu, Zvonimir Rakamaric
     SEFM 2007

[17] Arithmetic strengthening for shape analysis
     Stephen Magill, Josh Berdine, Edmund Clarke, and Byron Cook.
     SAS 2007

[18] Proving that programs eventually do something good
     Byron Cook et al
     POPL 2007

[19] Variance analyses from invariance analyses
     Josh Berdine et al
     POPL 2007

[20] Automatic termination proofs for programs with shape-shifting heaps
     Josh Berdine, Byron Cook, Dino Distefano, and Peter O'Hearn
     CAV 2006

[21] Terminator: Beyond safety (short tool description paper)
     Byron Cook, Andreas Podelski, and Andrey Rybalchenko
     CAV 2006

[22] Termination proofs for systems code
     Byron Cook, Andreas Podelski, and Andrey Rybalchenko
     PLDI 2006

[23] Abstraction refinement for termination
     Byron Cook, Andreas Podelski, Andrey Rybalchenko
     SAS 2005

[24] A Complete Method of Sythesis of Linear Ranking Functions
     Andreas Podelski, Andrey Rybalchenko
     VMCAI 2004

[25] Multidimensional rankings, program termination, and complexity bounds
     of flowchart programs.
     Christophe Alias, Alain Darte, Paul Feautrier, and Laure Gonnord.
     SAS 2010

[26] Aaron Bradley, Zohar Manna, Henni Sipma
     The polyranking principle.
     ICALP 2005

[27] Aaron Bradley, Zohar Manna, Henni Sipma
     Linear ranking with reachability
     CAV 2005

[28] Lazy abstraction with interpolants
     Ken McMillan
     CAV 2006

[29] Constraint solving for interpolation
     Andrey Rybalchenko, Viorica Sofronie-Stokkermans
     VMCAI 2007

[30] The octagon abstract domain
     Antoine Mine
     Higher-Order and Symbolic Computation 19(1): 31-100 (2006)

[31] Abstract interpretation: A unified lattice model for static analysis of
     programs by construction or approximation of fixpoints
     Patrick Cousot, Radhia Cousot
     POPL 1977

[32] Static determination of dynamic properties of programs
     Patrick Cousot, Radhia Cousot
     Int. Symp. on Programming, 1976

[33] A fast algorithm for finding dominators in a flowgraph
     Thomas Lengauer and Robert Endre Tarjan
     TOPLAS 1 (1): 121–141, 1979

[34] Faster Temporal Reasoning for Infinite-State Programs
     Byron Cook, Heidy Khlaaf, and Nir Piterman.
     FMCAD 2014. To Appear.

[35] Design and synthesis of synchronization skeletons using branching time temporal logic
     E. Clarke and E. Emerson
     Workshop on Logic of Programs, 1981.

[36] Automated Detection of Non-Termination and NullPointerExceptions for Java Bytecode
     M. Brockschmidt and T. Stroeder and C. Otto and J. Giesl
     FoVeOOS 2011
