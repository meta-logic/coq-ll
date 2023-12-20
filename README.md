
# Propositional and First Order Linear Logic in Coq

We formalize in Coq different sequent calculi for propositional and first order linear logic (LL) and we prove them to be equivalent. We also prove some meta-theorems, including cut-elimination and the completeness of the focused system. The focused system can be then used for proving adequacy between LL and (logical / computational) systems encoded in LL. See for instance the example in ./FOLL/Examples/LJLL.v

More details in <a href="https://www.sciencedirect.com/science/article/pii/S157106611830080X">this paper </a>.

This package is free software; you can redistribute it and/or modify it under the terms of GNU Lesser General Public License (see the COPYING file).

Author  <a href="mailto: bruno_xavier86@yahoo.com.br">Bruno Xavier</a>
and <a href="mailto:carlos.olarte@gmail.com"> Carlos Olarte</a>


## Getting Started

The project was tested with Coq 8.14 to 8.19 (thanks to Olivier Laurent!). No extra library is needed for compilation.

There are two main directories

 - PLL : Formalizing propositional linear logic.
 - FOLL : Formalizing first order linear logic.

 In both directories, the source files can be compiled with

```
make
```

and the HTML documentation can be generated with 

```
make html
```


