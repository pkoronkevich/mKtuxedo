# mKtuxedo
Ben and Paulette's final project for B522.

Formalizing the Semantics of microKanren

 We would like to use Agda to formalize the semantics of miniKanren, specifically the most concise implementation of miniKanren, called µKanren (found at https://github.com/jasonhemann/microKanren) , done by Jason Hemann and Dan Friedman with their 2013 paper µKanren: A Minimal Functional Core for Relational Programming.
	
 This project will consist of formalizing the functions running under the hood in µKanren. The core language has essentially 5 core functions that together perform unification: walk, unify, call/fresh, mplus, and bind. In addition, 3 essential forms make up the language: ==, disj, and conj, which use these internal functions. And then there are higher-level forms, like run, conde, condu, and fresh, but including several others, which are built on top of these core forms (some are functions, and some are macros).

A possible itinerary:

Part 1 (goal 1): Formalize the 5 core functions above. This, at a minimum, will consist of a proof that the unification algorithm is correct.

Part 2 (goal 2): Formalize the higher-level forms, like conde, etc. This will allow use to then a) make a relation Eval function, and b) find some nice proofs about the high-level language: canonical equivalences of programs, or other things.

Part 3 (far-reaching final goal): Impose a type-system for the higher-level forms, and prove type-safety. (A note -- this goal is a little fuzzy for us. Since there is no notion of types in microKanren, we aren’t quite sure what a type-safety proof would look like. If we get this far, or otherwise, we’d greatly benefit from talking to you about the role types play in unification, or in how you could see types coming into play here.)

Other papers /ideas suggested to us by Weixi:

-- for tips on how to handle general recursion
http://www.cs.nott.ac.uk/~pszvc/publications/General_Recursion_MSCS_2005.pdf

-- we might try ‘feuling’ -- another approach to handle general recursion. Feuling, at first glance, sounds similar to your use of Agda.Size, to use an outside notion of size to prove termination. (Weixi said that you typically find a clever way to map your data to Integers?)
