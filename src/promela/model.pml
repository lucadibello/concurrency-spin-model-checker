// Define the maximum number of elements in the array
#define MAX 10
#define LENGTH 3

// Define the variables
int a[LENGTH];

// Keep track of result of both versions of the program
int sequentialFrequencies[MAX + 1];
int sequentialMostFrequentValue = -1;
bit sequentialDone = 0;

init {
	// Initialize the array non-deterministically
	int i;
	for (i : 0 .. LENGTH - 1) {
		// Select a random value for the array
		int v;
		select(v : 0 .. MAX);
    printf("New value for v: %d\n", v);
		// Assign the value to the array
		a[i] = v;
    printf("i: %d, value: %d\n", i, a[i]);
	}

  // Print the array
  for (i : 0 .. LENGTH - 1) {
    printf("a[%d]: %d\n", i, a[i]);
  }

	// Run the sequential version of the program
	run sequentialCounter();
}

// Define both the sequential and parallel processes
proctype sequentialCounter() {
	int maxFrequency = -1;

	int k;
	for (k : 0 .. LENGTH - 1) {
		int value = a[k];
		sequentialFrequencies[value] = sequentialFrequencies[value] + 1;
		if
			:: sequentialFrequencies[value] > maxFrequency -> 
				maxFrequency = sequentialFrequencies[value];
				sequentialMostFrequentValue = value;
      :: else -> skip;
		fi
	}
  
  // Signal that the sequential version is done
  sequentialDone = 1;
}

// Properties to verify
// 1) Ensure that the sequential version eventually finishes
ltl p1 { <> (sequentialDone == 1) }
