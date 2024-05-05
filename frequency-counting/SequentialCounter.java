class SequentialCounter implements FrequentCounter
{
	 private int[] a;
	 private int max;
	 
	 public SequentialCounter(int[] a, int max) {
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

	 // number of occurrences of value `n` in `a`
	 protected int frequencyOf(int n) {
		  int frequency = 0;
		  for (int value: a) {
				if (value == n)
					 frequency += 1;
		  }
		  return frequency;
	 }

	 // most frequent integer in array
	 public int mostFrequent() {
		  int mostFrequent = -1;
		  int maxFrequency = -1;
		  int[] frequencies = new int[max + 1];
		  for (int k = 0; k < a.length; k++) {
				int value = a[k];
				frequencies[value] += 1;
				int frequency = frequencies[value];
				if (frequency > maxFrequency) {
					 mostFrequent = value;
					 maxFrequency = frequency;
				}
		  }
		  return mostFrequent;
	 }

}
