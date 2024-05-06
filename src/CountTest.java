public class CountTest
{
	 private int testSequential(int[] a, int max) {
		  SequentialCounter s = new SequentialCounter(a, max);
		  return s.mostFrequent();
	 }

	 private int testParallel(int[] a, int max) {
		  ParallelCounter s = new ParallelCounter(a, max);
		  return s.mostFrequent();
	 }

	 private boolean check(int[] a, int max) {
		  int s = testSequential(a, max);
		  int p = testParallel(a, max);
		  boolean result = (s == p);
		  if (result)
				System.out.println("Success: (" + s + "/" + p + ")");
		  else
				System.out.println("FAILURE: (" + s + "/" + p + ")");
		  return result;
	 }

	 void test1() {
		  int[] a = {1, 2, 3, 4, 2, 6};
		  check(a, 10);
		  check(a, 6);
		  check(a, 8);
	 }

	 void test2() {
		  int[] a = {1, 0, 3, 3, 5, 6, 7};
		  check(a, 10);
		  check(a, 7);
	 }

	 void test3() {
		  int[] a = { 3 };
		  check(a, 3);
		  check(a, 5);
		  check(a, 6);
	 }

	 void test4() {
		  int[] a = { 4, 1, 4, 2, 0 };
		  check(a, 4);
		  check(a, 5);
		  check(a, 6);
	 }

	 void test5() {
		  int[] a = { 1, 1, 1, 1, 1 };
		  check(a, 1);
		  check(a, 2);
		  check(a, 3);
	 }

	 void test6() {
		  int[] a = { 0 };
		  check(a, 1);
		  check(a, 2);
		  check(a, 3);
	 }
	 
	 public static void main(String[] args) {
		  var o = new CountTest();
		  o.test1();
		  o.test2();
		  o.test3();
		  o.test4();
		  o.test5();
		  o.test6();
	 }
}
