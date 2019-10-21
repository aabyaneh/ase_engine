Shared variables and headers in `msiiad.h`, `msiiad.c` and `pse.h` should be adapted.
`pse.h` header should be added to `phantom.c` and `msiiad.c`.

### There are two approaches:
* `pse_1`: Just send query to the external probabilistic solver for true branch. The probability for false branch can be computed form probability of true branch. Since the solver returns approximate probabilities may not be nice.
* `pse_2`: Send query to the external probabilistic solver for both true and false branches.