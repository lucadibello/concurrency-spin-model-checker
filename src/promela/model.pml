// Define the maximum number of elements in the array
#define MAX 10
#define LENGHT 100

// Define the variables
int a[LENGTH];

// Keep track of result of both versions of the program
int sequentialFrequencies[MAX + 1];
int sequentialMostFrequentValue;

init {
	// Initialize the array non-deterministically
	int i;
	for (i : 0 .. MAX) {
		// Select a random value for the array
		int v;
		select(v: 0 .. MAX)
		// Assign the value to the array
		a[i] = v;
	}

	// Run the sequential version of the program
	run sequentialCounter();
}

// Define both the sequential and parallel processes
proctype sequentialCounter() {
	int mostFrequent = -1;
	int maxFrequency = -1;
	int frequencies[MAX + 1];

	int k;
	for (k : 0 .. MAX) {
		int value = a[k];
		frequencies[value] = frequencies[value] + 1;
		if
			:: frequencies[value] > maxFrequency -> 
				maxFrequency = frequencies[value];
				mostFrequent = value;
		fi
	}

	// Save the most frequent value found by the sequential version
	sequentialMostFrequentValue = mostFrequent;

	// Save the array of frequencies found by the sequential version
	int i;
	for (i : 0 .. MAX) {
		sequentialFrequencies[i] = frequencies[i];
	}
}