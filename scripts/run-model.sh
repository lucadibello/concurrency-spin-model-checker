#!/bin/sh

# Create a output directory to store the files created by Spin
mkdir -p output && rm -rf output/* && cd output

ltls=(
  "termination"
  "sumCounts"
  "sameResult"
  "seqBeforePar"
  "alwaysSameResult" # this property will not hold
)

# Build the model using Spin + check for errors
echo "Building the ProMeLa model..."
OUTPUT=$(spin -a ../src/promela/model.pml -N $ltl)
if [ $? -ne 0 ]; then
  echo "\t Error building the model. Check the output: $OUTPUT"
  exit 1
else
  echo "\t Success!"
fi

# Build the analyzer using gcc + check for errors
echo "Building the analyzer..."
OUTPUT=$(gcc -Wno-format-overflow -DNFAIR=6 -o analyzer pan.c 2>&1)
if [ $? -ne 0 ]; then
  echo "\t Error building the analyzer. Check the output: $OUTPUT"
  exit 1
else
  echo "\t Success!"
fi

echo "Starting the analysis, checking ${#ltls[@]} LTL properties..."

# For each available Linear Temporal Logic (LTL) property, check it using the analyzer
counter=1 # Keep track of total checked LTL properties
totSuccess=0 # Keep track of successful LTL properties
for ltl in "${ltls[@]}" 
do
  echo "[$counter/${#ltls[@]}] Checking LTL property: $ltl"
  # Run the analyzer with the -a flag to check for assertion violations
  # -a = check for assertion violations
  # -f = check for LTL properties
  # -N = specify the LTL property to check
  ./analyzer -a -f -N $ltl > /dev/null

  # If user has requested to stop the script if a violation is found
  if [ $? -eq 1 ]; then
    echo "\t Run stopped by user... aborting..."
    exit 1
  fi

  # If there is a violation, a trace will be generated in the output directory
  # So, if the file exists, run spin again to get the counterexample
  if [ -f ./model.pml.trail ]; then
    echo "\t Counterexample found for $ltl. Running Spin to generate the trail file..."
    spin -k ./model.pml.trail ../src/promela/model.pml

    # If we have found a counterexample, we can stop the loop and exit the script
    echo "Exiting..."
    exit 1
  else
    echo "\t Success! No counterexample found for $ltl"
    totSuccess=$((totSuccess+1))
  fi

  # Increase the counter
  counter=$((counter+1))
done

# Print report
echo "Analysis finished. $totSuccess/$[counter-1] LTL properties checked successfully."

