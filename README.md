# Overview

This repository originates from the discipline PCA/2022 of the UnB PPGI. Parser, Lexer and Control-Flw Graphs were developed for the analyses:

 - Available Expressions Analysis
 - Reaching Definitions Analysis
 - Very Busy Expressions Analysis
 - Live Variables Analysis

### What is Data Flow Analysis?

*"In Data Flow Analysis it is customary to think of a program as a graph: the nodes are the elementary blocks and the edges describe how control can pass from one elementary block to another."*[1] 

We can say that:
 - Static analysis reasoning about flow of data in program
 - Different kinds of datra: constants, variables, expressions
 - Use by bug-finding tools and compilers

### Intraprocedural Analysis
Analysis performed within a single procedure or function, which examines the behavior of the program in a specific context, considering only the declarations and expressions of that procedure.

### The While Language
It is a simple imperative language. A WHILE program will be a sequence of statements.

Example:

    x = 5;
    y = 1;
    while (x != 1) {
	    y = x* y;
	    x = x - 1;
	}

### Available Expressions Analysis
The goal is to avoid recomputing expressions. *"For each program point, which expressions must have already been computed, and not later modified, on all paths to the program point*"[1].

Avoid recomputing expressions.

### Reaching Definitions Analysis

Here we want to find the use of uninitialized variables; determine which assignments can most accurately reach each point in the program, and check which assignments have been made and not replaced when program execution reaches that point along the way.

### Very Busy Expressions Analysis
*"An expression is very busy at the exit from a label if, no matter what path is taken from the label, the expression must always be used before any of the variables occurring in it are redefined."* [1]

Reduces code size. The objective is to calculate the expressions that are very busy in the output of each program point.

### Live Variables Analysis
*"A variable is live at the exit from a labei if there exists a path from the label to a use of the variable that does not re-define the variable."* [1]

Assign records efficiently. A variable is Live if there is a path to its name that does not reset it.

## OCaml 

OCaml (/oʊˈkæməl/ oh-KAM-əl, formerly Objective Caml) is a general-purpose, high-level multi-paradigm programming language which extends the Caml dialect of ML with object-oriented features. OCaml was created in 1996 by Xavier Leroy, Jérôme Vouillon, Damien Doligez, Didier Rémy, Ascánder Suárez, and others.

The OCaml toolchain includes an interactive top-level interpreter, a bytecode compiler, an optimizing native code compiler, a reversible debugger, and a package manager (OPAM). OCaml was initially developed in the context of automated theorem proving, and has an outsize presence in static analysis and formal methods software. Beyond these areas, it has found serious use in systems programming, web development, and financial engineering, among other application domains.

The acronym CAML originally stood for Categorical Abstract Machine Language, but OCaml omits this abstract machine.[3] OCaml is a free and open-source software project managed and principally maintained by the French Institute for Research in Computer Science and Automation (Inria). In the early 2000s, elements from OCaml were adopted by many languages, notably F# and Scala. 
***Source: Wikipedia***


### Code example with OCalm

Here is a simple OCaml code example that defines a function to calculate the factorial of a number:

    let rec factorial n =
	    if n <=1 then 1
	    else n* factorial (n - 1)

	  let() = 
		  let result = factorial 5 in
		  print_int result;
		  print_newline()

This code defines a function called `factorial` that uses recursion to calculate the factorial of an integer `n`. The function is defined using the `let` keyword, followed by the function name and its parameters. The `rec` keyword indicates that the function is recursive. The function uses an `if...then...else` expression to check if `n` is less than or equal to 1, in which case it returns 1. Otherwise, the function calls itself with a reduced argument by 1 and multiplies the result by the original number.

The last part of the code uses the `factorial` function to calculate the factorial of 5 and store the result in a variable called `result`. Then, the code calls two output functions to print the result to the screen.

Note that OCaml code is sensitive to indentation, so formatting is important. Also, the program begins with a special `let () = ...` function, which defines the entry point of the program.

### How to install Ocaml
We thank Professor Michael R. Clarkson et al. [2]. They gave us a good explanation of how to install Ocaml (https://cs3110.github.io/textbook/chapters/preface/install.html) and an excellent tutorial on how to use it. 


### How to use our project

In this project, we used the Ocamlbuild. The builds are set in the Makefile, with one configuration for each analysis. In the sub-folder programs, we have the codes of some programs used as examples in the book [1]. Each analysis uses one program as a default, but one can set a new program as a parameter of the analysis.

	Example of how to implement the Reaching Definition analysis:
		# Clean up the project. It's not essential
				make clean  

		# Build the analysis
				make rd

		# Execute de analysis
				./rd_analysis.code

		# Expected results (see page 46 of [1])
				REACHING DEFINITION ANALYSIS:
				Entry (1): {(x, ?)(y, ?)}
				Exit (1): {(x, 1)(y, ?)}
				Entry (2): {(x, 1)(y, ?)}
				Exit (2): {(x, 1)(y, 2)}
				Entry (3): {(x, 1)(x, 5)(y, 2)(y, 4)}
				Exit (3): {(x, 1)(x, 5)(y, 2)(y, 4)}
				Entry (4): {(x, 1)(x, 5)(y, 2)(y, 4)}
				Exit (4): {(x, 1)(x, 5)(y, 4)}
				Entry (5): {(x, 1)(x, 5)(y, 4)}
				Exit (5): {(x, 5)(y, 4)}
				GENERATED DATA FLOW GRAPH:
				1: 2
				2: 3
				3: 4
				4: 5
				5: 3

		# If one wants to evaluate other file than the default
				./rd_analysis.byte "full path of the new while language program"

## Referências
[1] NIELSON, Flemming; NIELSON, Hanne R.; HANKIN, Chris. Principles of program analysis. Springer, 2005.
[2] Michael R. Clarkson et al. OCaml Programming: Correct + Efficient + Beautiful - 2013 - accessed Feb 2023 - https://cs3110.github.io/textbook
