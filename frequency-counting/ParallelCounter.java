import java.util.ArrayList;

class ParallelCounter implements FrequentCounter
{
	 private int[] a;
	 private int max;

	 public ParallelCounter(int[] a, int max) {
		  setArray(a);
		  this.max = max;
	 }

	 // set array to be searched
	 public void setArray(int[] a) {
		  this.a = a;
	 }

	 // get current array
	 public int[] array() {
		  return a;
	 }

	 // most frequent integer in array
	 public int mostFrequent() {
		  ArrayList<Thread> threads = new ArrayList<>();
		  ArrayList<ThreadedCounter> targets = new ArrayList<>();
		  for (int n = 0; n <= max; n++) {
				ThreadedCounter c = new ThreadedCounter(a, n, max);
				targets.add(c);
				Thread t = new Thread(c);
				threads.add(t);
				// start the thread
				t.start();
		  }
		  // wait for all threads to terminate
		  int mostFrequent = -1;
		  int maxFrequency = -1;
		  for (int k = 0; k < threads.size(); k++) {
				try {
					 Thread t = threads.get(k);
					 // wait for thread t to terminate
					 t.join();
					 // collect its result and combine it with the others
					 var c = targets.get(k);
					 int frequency = c.frequency();
					 if (frequency > maxFrequency) {
						  mostFrequent = k;
						  maxFrequency = frequency;
					 }
				} catch (InterruptedException s) {
					 System.out.println("Thread interrupted");
				}
		  }
		  return mostFrequent;
	 }
}


class ThreadedCounter extends SequentialCounter implements Runnable
{
	 private int frequency;
	 private int n;
	 
	 ThreadedCounter(int[] a, int n, int max) {
		  super(a, max);
		  this.n = n;
	 }

	 public void run() {
		  frequency = frequencyOf(n);
	 }

	 public int frequency() {
		  return frequency;
	 }
}
