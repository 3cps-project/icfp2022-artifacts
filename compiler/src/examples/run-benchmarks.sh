#!/bin/sh
#
# Script to run the compiler on the benchmarks and then gather statistics about
# the analysis.
#
# usage:
#	run-benchmarks.sh [--run] [--trial n]
#

usage() {
  echo "usage: run-benchmarks.sh [--run] [--trial n]"
  exit 1
}

if test x"$1" = x--run ; then
  # run the interpreter
  RUN=yes
  CHK_FLAG="--check-analysis-results"
  SUFFIX="-run"
  shift
else
  RUN=no
  CHK_FLAG=""
  SUFFIX=""
fi

if test x"$1" = x--trial ; then
  shift
  if test x"$1" = x ; then
    usage
  fi
  SUFFIX="$SUFFIX"-"$1"
fi

SMLC=../../bin/smlc
SMLC_FLAGS="--json --disable-warnings --disable-check-simple --dump-analysis-results"

# run_smlc PROG FLAGS RESULT
run_smlc() {
  SRC="$1.sml"
  $SMLC $SMLC_FLAGS $CHK_FLAG $2 $SRC
  mv $1.json $3.json
}

PROGS="\
  ack \
  boyer \
  cps-convert \
  cpstak \
  derivative \
  filter \
  interpreter \
  knuth-bendix \
  life \
  mandelbrot \
  nqueens \
  parser-comb \
  quicksort \
  raytracer \
  smith-normal-form \
  tak \
  tsp \
"

# the interpreter takes too long on these
#
EXTRA_PROGS="\
  k-cfa \
  mc-ray \
  nucleic \
  ratio-regions \
  safe-for-space \
"

if [ $RUN = yes ] ; then
  ALL_PROGS="$PROGS"
else
  ALL_PROGS="$PROGS $EXTRA_PROGS"
fi

for f in $ALL_PROGS ; do
  echo "***** $f"
  #
  # first run w/o simple optimizations, but only for timing results
  #
  if [ $RUN != yes ] ; then
    run_smlc $f --disable-simple-opt $f-noopt"$SUFFIX"
  fi
  #
  # then run w/ simple optimizations
  #
  run_smlc $f "" $f-opt"$SUFFIX"
done

exit 0
