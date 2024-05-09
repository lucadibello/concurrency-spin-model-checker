// Define the maximum number of elements in the array
#define MAX 2
#define LENGTH 2

// Define the variables
int a[LENGTH];

// Keep track of result of both versions of the program
int sequential_counts[MAX + 1];
int parallel_counts[MAX + 1];
int sequential_result = -1;
int parallel_result = -1;

// Keep track of the status of both versions of the program
bit sequentialDone = 0;
bit parallelDone = 0;

init {
	// Initialize the array non-deterministically
  printf("Random state:\n")
	int i;
	for (i : 0 .. LENGTH - 1) {
		// Select a random value for the array
		int v;
		select(v : 0 .. MAX);
		// Assign the value to the array
		a[i] = v;

    // Print the value
    printf("\ta[%d] = %d\n", i, v);
	}

	// Run the sequential version of the program
  printf("Running sequential version...\n");
	run sequentialCounter();
 
  // Run the parallel version of the program
  printf("Running parallel version...\n");
  run parallelCounter();
}

// Define both the sequential and parallel processes

// 1) Sequential version
proctype sequentialCounter() {
	int maxFrequency = -1;
	int k;
	for (k : 0 .. LENGTH - 1) {
		int value = a[k];
		sequential_counts[value] = sequential_counts[value] + 1;
		if
			:: sequential_counts[value] > maxFrequency -> 
				maxFrequency = sequential_counts[value];
				sequential_result = value;
      :: else -> skip;
		fi
	}
  // Signal that the sequential version is done
  sequentialDone = 1;
}

// 2) Parallel version
proctype parallelCounter() {
  // Create channel to wait for workers to finish
  chan joinCh = [MAX + 1] of { pid };

  // Create array of PID's for workers
  pid workers[MAX + 1];

  // Create a worker for each possible value
  int i;
  for (i : 0 .. MAX) {
    workers[i] = run parallelWorker(i, joinCh);
  }

  // Wait for all workers to finish
  for (i : 0 .. MAX) {
    int done;
    joinCh ? done;
  }
 
  printf("\t [!] all workers are done\n");

  // Now, look for the maximum frequency in the parallel counts array
  int mostFrequent = -1;
  int maxFrequency = -1;
  for (i : 0 .. MAX) {
    if
      :: parallel_counts[i] > maxFrequency ->
        maxFrequency = parallel_counts[i];
        mostFrequent = i;
      :: else -> skip;
    fi
  }
  // Save the result in the global state
  parallel_result = mostFrequent;
  // Signal that the parallel version is done
  parallelDone = 1;
}

// The worker process represents a thread that looks for the count of a specific value in the array
proctype parallelWorker(int value; chan out) {
  // Look for the value in the array
  int frequency = 0;
  int i;
  for (i : 0 .. LENGTH - 1) {
    if
      :: a[i] == value -> frequency = frequency + 1;
      :: else -> skip;
    fi
  }

  // Update the value in the parallel counts array
  parallel_counts[value] = frequency;
  printf("Worker for value %d is done\n", value);
  out ! _pid;
}

// Properties to verify
// 1) Ensure that the sequential version eventually finishes
ltl sequentialTermination { <> (sequentialDone == 1) }
ltl parallelTermination { <> (parallelDone == 1) }

