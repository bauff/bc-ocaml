# bc-ocaml
BC evaluator implemented in OCAML

### How to run
```
dune runtest
```
### Features of this implementation
- scopes are created per function call
- arguments and variable are assigned within their scope
- arguments and variables are accessed by recursively checking each scope defined in the entire programs environment starting with the local scope
- recursive functions
- special statements (`break`, `continue` and `return`) throw an exception when evaluated
- these exceptions are caught when evaluating statements nested within other, certain statements (`for`, `while`...) and are meant to  halt execution of code in some manner within the statement but preserve the state of the environment. 
- function calls catch `return e` exceptions and evaluates the expression `e`
- `while` and `for` loops catch `break` and `continue` exceptions
    * `break`  will exit the loop
    * `continue`  will skip all subsequent statements within the loop and start to evaluate the condition of the next loop

