[![Build Status](https://travis-ci.com/jsalzbergedu/pegreg.svg?branch=master)](https://travis-ci.com/jsalzbergedu/pegreg) 
[![License](http://img.shields.io/badge/Licence-MIT-brightgreen.svg)](LICENSE)
[![Lua](https://img.shields.io/badge/Lua-5.2%2C%205.3%2C%20MoonJIT-blue.svg)]()
[![Coverage Status](https://coveralls.io/repos/github/jsalzbergedu/pegreg/badge.svg?branch=master)](https://coveralls.io/github/jsalzbergedu/pegreg?branch=master)

![Poster Explaining What PEGREG is](https://user-images.githubusercontent.com/25715167/101115874-12c0ad00-35b2-11eb-943d-601b77c32d2e.png)

# PEGREG
A lua library for compiling a subset of PEGs to FSTs.
Requires fst-fast-system (an NFST interpreter) and fst-fast (a lua library wrapping fst-fast-system).

# Roadmap
For arbitrary regular expressions or string literals A and B, this library
turns A/B, AB, and A* into DFAs quite well.
However, this library aims to make A/B and A* _possessive_, and allow
linear-time matching and capture.
Therefore, there are still two major items on the roadmap before this library can
be made a part of Rosie:

1. Possessiveness.
This will require queries that can find the following:
- [X] The DFA of an NFA
- [X] The states that ought to be demoted (their outgoing arrows ignored)
- [ ] The arrows that ought to be ignored
- [ ] The NFA resulting from removing those arrows

And interpreters (AST transformers) that can generate
- [X] NFAs from each subexpression of the AST
- [ ] DFAs from each sub-nfa
- [ ] B substates from each subexpression
- [ ] B states from each subexpression
- [ ] B subarrows from each subexpression
- [ ] B arrows from each subexpression
- [ ] The possessive NFA that results from removing the forbidden b arrows.

2. Matching subexpressions
This library intends to use Danny Dubé and Marc Feely's method of extracting
matches from DFAs, described in these two papers:
[Efficiently building a parse tree from a regular expression](https://www.iro.umontreal.ca/~feeley/papers/DubeFeeleyACTAINFORMATICA00.pdf)
[Automatic construction of parse trees for lexemes](http://www.schemeworkshop.org/2006/14-dube.pdf)
And implemented in [SILex](https://code.call-cc.org/svn/chicken-eggs/release/5/silex/trunk/silex.scm)

to do this, we need

- [ ] A backend that can accept `push`, `snoc`, and `sel`, instead of DFSTs operating from chars to char
- [ ] A frontend that emits those instructions instead of DFSTs from char to char

# Interpreter Style
Each interpreter in PEGREG's interpreter chain forms a [tagless final interpreter](https://www.cs.utexas.edu/~wcook/Drafts/2012/ecoop2012.pdf).

And the FST uses a version of [finite state transducers](https://www.cs.jhu.edu/~jason/405/lectures1-2/sld001.htm).
