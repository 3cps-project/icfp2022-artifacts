Paper: Analyzing Binding Extent in 3CPS.
This artifact contains the current implementation of the compiler for 3CPS.

# Build Instructions

Assume that we start with the base VM provided by ICFP.

## Prerequisites

### Build Tools

```shell
sudo apt-get install gcc make autoconf python3
```

### Standard ML of New Jersey

```shell
sudo mkdir /usr/local/smlnj
cd /usr/local/smlnj
sudo wget https://smlnj.org/dist/working/110.99.2/config.tgz
sudo tar -xzf config.tgz
sudo ./config/install.sh
PATH="$PATH":/usr/local/smlnj/bin
```

## Building the Artifact

Make sure SML/NJ is on your path.

```shell
cd ~/compiler
autoconf -Iconfig
./configure
(cd src/compiler; make)
```


## Running the Experiments

The command `./src/test-compiler` runs the compiler on all test programs. 
This will create and `cat` a log file in `src/examples` for each program. This log file will be empty if no options are provided.

To build Table 1 from the paper, use the command
```shell
./src/test-compiler --flags json
echo "dumpTable();" | sml extract-table.sml
```
To build the table that reports dynamic binding information, run the command
```shell
./src/test-compiler --flags json check-analysis-results dump-allocation-summary
echo "dumpDynamicTable();" | sml extract-table.sml
```

### General use

For inspection of a single file, use the command `./src/test-compiler --input_file FILE` where `FILE` is the path to the single file. The flag `--show-stdout` can also be passed in order to view the output of the compiler. If you are defining you own examples and have syntax errors, this will display them.


```shell
./src/test-compiler --flags FLAGS
```
To populate the log file, where FLAGS can be any of
- `timing`: dumps the timing results of the compiler. The time taken for the extent analysis is to the right of `extent analysis ...` under the `Total` column.
- `dump-extent-summary`: dumps the promotion rates directly to the log file.
- `json`: - dump a JSON file for each program in `src/examples` with detailed information about the compiler's run. Search for the key "promotions" to find promotion results, and "timing" to find the timing results.

For more detailed use:
- `dump-cps`: dumps the CPS IR
- `dump-extents`: dumps the individual extents of each variable
- `disable-simple-opt`: disable the simple optimizations of the compiler
- `check-analysis-results`: check the results of the analysis using the intrumented interpreter
- `dump-allocation-summary`: include the dynamic binding allocation to the json

Multiple flags may be used. As an example:
```shell
./src/test-compiler --flags timing json dump-extent-summary
```

### Specific test cases

The file in `./src/examples/all-extents-example.sml` contains a short
test case that has a variable for every possible set of extents, along
with explanations of why this is the case for each variable.
In order to view this example's CPS and results, use the following command
```shell
./src/test-compiler --file ./src/examples/all-extents-example.sml --flags disable-simple-opt dump-cps dump-extents
```
The flag `disable-simple-opt` prevents these interesting variables
from being constant-folded away.
