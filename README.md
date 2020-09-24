[![Build Status](https://travis-ci.com/MetaCoq/metacoq.svg?branch=coq-8.11)](https://travis-ci.com/MetaCoq/metacoq)
[![MetaCoq Chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com)

MetaCoq is a project formalizing Coq in Coq and providing tools for
manipulating Coq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Coq.

**Quick jump**
- [Summary](#summary)
- [Documentation](#documentation)
- [Papers](#papers)
- [Team](#team--credits)
- [Installing](#installation-instructions)

News
====

["Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"](coqcoqcorrect),
Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau and Théo Winterhalter, POPL 2020.

Project Summary
===============

At the center of this project is the Template-Coq quoting library for
Coq. The project currently has a single repository extending
Template-Coq with additional features. Each directory has a `README.md` file
describing its organization.

[Template-Coq](https://github.com/MetaCoq/metacoq/tree/master/template-coq/theories)
-------------

Template-Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes `Coq` terms and constructs a representation of their syntax tree as
a `Coq` inductive data type. The representation is based on the kernel's
term representation.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

- A monad for manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the style of MTac.

[Checker](https://github.com/MetaCoq/metacoq/tree/master/checker/theories)
-------

A partial type-checker for the Calculus of Inductive Constructions,
whose extraction to ML is runnable as a plugin (using command `MetaCoq
Check foo`). This checker uses _fuel_, so it must be passed a number
of maximal reduction steps to perform when calling conversion, and is
NOT verified.

[PCUIC](https://github.com/MetaCoq/metacoq/tree/master/pcuic/theories)
-----

PCUIC, the Polymorphic Cumulative Calculus of Inductive Constructions is
a cleaned up version of the term language of Coq and its associated
type system, equivalent to the one of Coq. This version of the
calculus has proofs of standard metatheoretical results:

- Weakening for global declarations, weakening and substitution for
  local contexts.

- Confluence of reduction using a notion of parallel reduction

- Context conversion and validity of typing.

- Subject Reduction (case/cofix reduction excluded) 

- Principality: every typeable term has a smallest type.

- Elimination restrictions: the elimination restrictions ensure
  that singleton elimination (from Prop to Type) is only allowed
  on singleton inductives in Prop.

[Safe Checker](https://github.com/MetaCoq/metacoq/tree/master/safechecker/theories)
-----

Implementation of a fuel-free and verified reduction machine, conversion
checker and type checker for PCUIC. This relies on a postulate of 
strong normalization of the reduction relation of PCUIC on well-typed terms.
The extracted safe checker is available in Coq through a new vernacular command:

    MetaCoq SafeCheck <term>

After importing `MetaCoq.SafeChecker.Loader`.

To roughly compare the time used to check a definition with Coq's vanilla
type-checker, one can use:

    MetaCoq CoqCheck <term>

[Erasure](https://github.com/MetaCoq/metacoq/tree/master/erasure/theories)
----------

An erasure procedure to untyped lambda-calculus accomplishing the
same as the Extraction plugin of Coq. The extracted safe erasure is
available in Coq through a new vernacular command:

    MetaCoq Erase <term>

After importing `MetaCoq.Erasure.Loader`.

[Translations](https://github.com/MetaCoq/metacoq/tree/master/translations)
------------

Examples of translations built on top of this:

- a parametricity plugin in [translations/param_original.v](https://github.com/MetaCoq/metacoq/tree/master/translations/param_original.v)
- a plugin to negate funext in [translations/times_bool_fun.v](https://github.com/MetaCoq/metacoq/tree/master/translations/times_bool_fun.v)

Documentation
=============

- You may want to start with a [demo](https://github.com/MetaCoq/metacoq/tree/master/examples/demo.v)
- The current master branch [documentation (as light coqdoc files)](html/toc.html).
- An example Coq plugin built on the Template Monad, which can be used to
  add a constructor to any inductive type is in [examples/add_constructor.v](https://github.com/MetaCoq/metacoq/tree/master/examples/add_constructor.v)
- The test-suite files [test-suite/erasure_test.v](https://github.com/MetaCoq/metacoq/tree/master/test-suite/erasure_test.v)
  and [test-suite/safechecker_test.v](https://github.com/MetaCoq/metacoq/tree/master/test-suite/safechecker_test.v) show example
  uses (and current limitations of) the verified checker and erasure.

ident vs. qualid. vs kername
---------------------------

MetaCoq uses three types convertible to `string` which have a different intended meaning:

- `ident` is the type of identifiers, they should not contains any dot.
  E.g. `nat`

- `qualid` is the type of partially qualified names.
  E.g. `Datatypes.nat`

- `kername` is the type of fully qualified names.
  E.g. `Coq.Init.Datatypes.nat`

Quoting always produce fully qualified names. On the converse, unquoting allow to
have only partially qualified names and rely on Coq to resolve them. The commands
of the TemplateMonad also allow partially qualified names.

Options
-------

`Set / Unset Strict Unquote Universe Mode`. When this mode is on,
the unquoting of a universe level fails if this level does not exists.
Otherwise the level is added to the current context. It is on by default.

There is also an "opaque" universe `fresh_universe` which is unquoted to
a fresh level when `Strict Unquote Universe Mode` is off.

Dependency graph between files
------------------------------

Generated on 2020/09/24, sources [there](https://github.com/MetaCoq/metacoq/tree/master/dependency-graph).

<center>
<img src="https://raw.githubusercontent.com/MetaCoq/metacoq.github.io/master/assets/depgraph-2020-09-24.png"
	 alt="Dependency graph" width="700px" display="inline"/>
</center>



Papers
======

- ["Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"](coqcoqcorrect)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau
  and Théo Winterhalter. POPL 2020, New Orleans.
  
- ["Coq Coq Codet! Towards a Verified Toolchain for Coq in
  MetaCoq"](http://www.irif.fr/~sozeau/research/publications/Coq_Coq_Codet-CoqWS19.pdf)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau and
  Théo Winterhalter. Abstract and
  [presentation](http://www.ps.uni-saarland.de/~forster/downloads/slides-coqws19.pdf)
  given at the [Coq Workshop
  2019](https://staff.aist.go.jp/reynald.affeldt/coq2019/), September
  2019.

- ["The MetaCoq Project"](https://www.irif.fr/~sozeau/research/publications/drafts/The_MetaCoq_Project.pdf)
  Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster, Fabian Kunze,
  Gregory Malecha, Nicolas Tabareau and Théo Winterhalter. JAR, February 2020.
  Extended version of the ITP 2018 paper.

  This includes a full documentation of the Template Monad and the typing rules of PCUIC.

- [A certifying extraction with time bounds from Coq to call-by-value λ-calculus](https://www.ps.uni-saarland.de/Publications/documents/ForsterKunze_2019_Certifying-extraction.pdf).
  Yannick Forster and Fabian Kunze.
  ITP 2019.
  [Example](https://github.com/uds-psl/certifying-extraction-with-time-bounds/blob/master/Tactics/Extract.v)

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://hal.archives-ouvertes.fr/hal-01809681/document)
  Abhishek Anand, Simon Boulier, Cyril Cohen, Matthieu Sozeau and Nicolas Tabareau.
  ITP 2018.

- The system was presented at [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)

Team & Credits
=======

<center>
<figure><img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/abhishek-anand.jpg"
alt="Abhishek Anand" width="150px" display="inline"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/danil-annenkov.jpeg"
alt="Danil Annenkov" width="150px" display="inline"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/simon-boulier.jpg"
alt="Simon Boulier" width="150px"/><br/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/cyril-cohen.png"
alt="Cyril Cohen" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/yannick-forster.jpg"
alt="Yannick Forster" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/gregory-malecha.jpg"
alt="Gregory Malecha" width="150px"/><br/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/matthieu-sozeau.png"
alt="Matthieu Sozeau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/nicolas-tabareau.jpg"
alt="Nicolas Tabareau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/theo-winterhalter.jpg"
alt="Théo Winterhalter" width="150px"/>

<figcaption>MetaCoq is developed by (left to right) 
<a href="https://github.com/aa755">Abhishek Anand</a>,
<a href="https://github.com/annenkov">Danil Annenkov</a>,
<a href="https://github.com/simonboulier">Simon Boulier</a>,
<a href="https://github.com/CohenCyril">Cyril Cohen</a>,
<a href="https://github.com/yforster">Yannick Forster</a>,
<a href="https://github.com/gmalecha">Gregory Malecha</a>,
<a href="https://github.com/mattam82">Matthieu Sozeau</a>,
<a href="https://github.com/Tabareau">Nicolas Tabareau</a> and
<a href="https://github.com/TheoWinterhalter">Théo Winterhalter</a>.
</figcaption>
</figure>
</center>

```
Copyright (c) 2014-2020 Gregory Malecha
Copyright (c) 2015-2020 Abhishek Anand, Matthieu Sozeau
Copyright (c) 2017-2020 Simon Boulier, Nicolas Tabareau, Cyril Cohen
Copyright (c) 2018-2020 Danil Annenkov, Yannick Forster, Théo Winterhalter
```

This software is distributed under the terms of the MIT license.
See [LICENSE](https://github.com/MetaCoq/metacoq/tree/master/LICENSE) for details.

Bugs
====

Please report any bugs (or feature requests) on the github [issue tracker](https://github.com/MetaCoq/metacoq/issues).


Installation instructions
=========================

Installing with OPAM
-----------------

The easiest way to get all packages is through [`opam`](http://opam.ocaml.org).
See [Coq's opam documentation](https://coq.inria.fr/opam-using.html)
for installing an `opam` switch for Coq.
See [releases](https://github.com/MetaCoq/metacoq/releases) and 
[Coq's Package Index](https://coq.inria.fr/opam/www/) for information on 
the available releases and opam packages. 

To add the Coq repository to available `opam` packages, use:

    # opam repo add coq-released https://coq.inria.fr/opam/released

To update the list of available packages at any point use:

    # opam update

Then, simply issue:

    # opam install coq-metacoq

MetaCoq is split into multiple packages that get all installed using the
`coq-metacoq` meta-package:

 - `coq-metacoq-template` for the Template Monad and quoting plugin
 - `coq-metacoq-checker` for the UNverified checker of template-coq terms
 - `coq-metacoq-pcuic` for the PCUIC development and proof of the
   Template-Coq -> PCUIC translation
 - `coq-metacoq-safechecker` for the verified checker on PCUIC terms
 - `coq-metacoq-erasure` for the verifed erasure from PCUIC to
   untyped lambda-calculus.
 - `coq-metacoq-translations` for example translations from type theory
   to type theory: e.g. variants of parametricity.

There are also `.dev` packages available in the `extra-dev` repository
of Coq, to get those you will need to activate the following repositories:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
    
Development
-----------

See the current development branch [README](https://github.com/MetaCoq/metacoq/tree/master)
file for developer installation instructions.
