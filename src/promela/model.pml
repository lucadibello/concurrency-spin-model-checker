// Define the maximum number of elements in the array
#define MAX 3
#define LENGTH 3

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
// Sum of the counts in both versions
int sumCountsSequential = 0;
int sumCountsParallel = 0;

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
  // Count the sum of the counts for the sequential version
  k = 0;
  for (k : 0 .. MAX) {
    sumCountsSequential = sumCountsSequential + sequential_counts[k];
  }
  // Signal that the sequential version is done
  sequentialDone = 1;

  // Print the result
  printf("[SEQUENTIAL] most frequent value in the array is %d\n", sequential_result);
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
  // Count the sum of the counts for the parallel version
  i = 0;
  for (i : 0 .. MAX) {
    sumCountsParallel = sumCountsParallel + parallel_counts[i];
  }
  // Signal that the parallel version is done
  parallelDone = 1;
  // Print the result
  printf("[PARALLEL] most frequent value in the array is %d\n", parallel_result);
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
// 1) Ensure that both the sequential and parallel version eventually finishes
ltl termination { <> (sequentialDone == 1 && parallelDone == 1) }
// 2) The sum of the counts in both versions should be equal to the length of the array
ltl sumCounts { [] (sequentialDone == 1 && parallelDone == 1) -> (sumCountsSequential == LENGTH && sumCountsParallel == LENGTH) }
// 3) The result of both versions should be the same
ltl sameResult { [] (sequentialDone == 1 && parallelDone == 1) -> (sequential_result == parallel_result) }
// 4) State of the execution (the sequential process is started before the parallel one)
ltl seqBeforePar { [](sequentialDone -> !parallelDone U parallelDone) }

// Property that SPIN is NOT able to verify as it is not true
ltl alwaysSameResult { [](sequential_result == parallel_result) }
