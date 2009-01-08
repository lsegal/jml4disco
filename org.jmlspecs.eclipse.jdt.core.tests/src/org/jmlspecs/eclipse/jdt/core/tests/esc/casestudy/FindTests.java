package org.jmlspecs.eclipse.jdt.core.tests.esc.casestudy;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class FindTests extends AbstractRegressionTest {
	public FindTests(String name) {
		super(name);
	}

	// Augment problem detection settings
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();

		options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlEsc, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
		options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		// options.put(JmlCompilerOptions.OPTION_SpecPath,
		// NullTypeSystemTestCompiler.getSpecPath());
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		return options;
	}

	private final String testsPath = "tests" + '\\' + "esc" + '\\' + "casestudy" + '\\';

	public void test_001_Find() {
		this.runNegativeTest(new String[] {
				testsPath + "Find.java",
				"package tests.esc.casestudy;\n" +
				"public class Find {\n" +
				"   /*@ ensures \\result == (\\forall int p, q; (0 <= p) & (p <= f) & (f <= q) & (q < A.length);\n" +
				"                                              (A[p] <= A[f]) & (A[f] <= A[q]));\n" +
				"      static boolean found(int[] A, int f) {\n" +
				"        return (\\forall int p, q; 0 <= p & p <= f & f <= q & q < A.length;\n" +
				"                                   A[p] <= A[f] && A[f] <= A[q]);\n" +
				"      }\n" +
				"     @*/\n" +
				"\n" +
				"\n" +
				"   /*@ ensures \\result == (m <= f & (\\forall int p, q; 0 <= p & p < m & m <= q & q < A.length;\n" +
				"     @                                                   A[p] <= A[q]));\n" +
				"     @ static boolean m_invariant(int m, int[] A, int f) {\n" +
				"     @    return (m <= f & (\\forall int p, q; 0 <= p & p < m & m <= q & q < A.length;\n" +
				"     @                                         A[p] <= A[q]));\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"   /*@ ensures \\result == (f <= n & (\\forall int p, q; 0 <= p & p <= n & n < q & q < A.length;\n" +
				"     @                                                   A[p] <= A[q]));\n" +
				"     @ static boolean n_invariant(int n, int[] A, int f) {\n" +
				"     @    return (f <= n & (\\forall int p, q; 0 <= p & p <= n & n < q & q < A.length;\n" +
				"     @                                         A[p] <= A[q]));\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"   /*@ ensures \\result == (m <= i & (\\forall int p; 0 <= p & p < i;\n" +
				"     @                                                A[p] <= r));\n" +
				"     @ static boolean i_invariant(int m, int n, int i, int r, int[] A) {\n" +
				"     @    return (m <= i & (\\forall int p; 0 <= p & p < i;\n" +
				"     @                                      A[p] <= r));\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"   /*@ ensures \\result == (j <= n & (\\forall int q; j < q & q < A.length;\n" +
				"     @                                                r <= A[q]));\n" +
				"     @ static boolean j_invariant(int m, int n, int j, int r, int[] A) {\n" +
				"     @    return (j <= n & (\\forall int q; j < q & q < A.length;\n" +
				"     @                                      r <= A[q]));\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"   /*@ ensures \\result == (i > m & j < n) || (i <= f && f <= j && A[f] == r);\n" +
				"     @ static boolean termination(int i, int j, int m, int n, int r, int[] A) {\n" +
				"     @    return (i > m & j < n) || (i <= f && f <= j && A[f] == r);\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"   /*@ requires t.length == t_.length\n" +  // this is new
				"     @ ensures \\result == (0 <= i && j < t.length &&\n" +
				"     @                      t[i] == t_[j] && t[j] == t_[i] &&\n" +
				"     @                      (\\forall int k; 0 <= k && k < t.length && k != i && k != j;\n" +
				"     @                                       t[k] == t_[k]));\n" +
				"     @ static boolean exchange(int[] t, int[] t_, int i, int j) {\n" +
				"     @    return (0 <= i && j < t.length &&\n" +
				"     @            t[i] == t_[j] && t[j] == t_[i] &&\n" +
				"     @            (\\forall int k; 0 <= k && k < t.length && k != i && k != j;\n" +
				"     @                             t[k] == t_[k]));\n" +
				"     @ }\n" +
				"     @*/\n" +
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"   //@ requires 0 <= f && f < A.length;\n" +
				"   //@ ensures (\\forall int p, q; 1 <= p && p <= f && f <= q && q < A.length;\n" +
				"                                   );\n" +
				"   public static int find(int[] A, int f)\n" +
				"   {\n" +
				"       int m = 1;\n" +
				"       int n = N;\n" +
				"       //@ maintaining m_invariant(m, A, f);\n" +
				"       //@ maintaining n_invariant(n, A, f);\n" +
				"       //@ maintaining permutation(A, \\old(A)));\n" +
				"       //@ maintaining 0 <= m & n < A.length;\n" +
				"       //@ decreasing n - m;\n" +
				"       while (m < n) {\n" +
				"             int r = A[f];\n" +
				"             int i = m;\n" +
				"             int j = n;\n" +
				"             //@ maintaining i_invariant(m, n, i, r, A, f);\n" +
				"             //@ maintaining j_invariant(m, n, j, r, A, f);\n" +
				"             //@ maintaining m_invariant(m, A, f);\n" +
				"             //@ maintaining n_invariant(n, A, f);\n" +
				"             //@ maintaining 0 <= j & i <= A.length;\n" +
				"             //@ maintaining termination(i, j, m, n, r, A, f);\n" +
				"             //@ maintaining permutation(A, \\old(A)));\n" +
				"             //@ decreasing a.length + 2 + j - i;\n" +
				"             while (i <= j) {\n" +
				"                   //@ ghost A_[] = copy(A);\n" +
				"                   //@ ghost i_ = i;\n" +
				"                   //@ ghost j_ = j;\n" +
				"                   //@ maintaining i_invariant(m, n, i, r, A, f);\n" +
				"                   //@ maintaining i_ <= i & i <= n;\n" +
				"                   //@ maintaining termination(i, j, m, n, r, A, f);\n" +
				"                   //@ decreasing a.length + 1 - i;\n" +
				"                   while (A[i] < r) {\n" +
				"                         i++;\n" +
				"                   }\n" +
				"\n" +
				"                   //@ maintaining j_invariant(m, n, i, r, A, f);\n" +
				"                   //@ maintaining j <= j_ & m <= j;\n" +
				"                   //@ maintaining termination(i, j, m, n, r, A, f);\n" +
				"                   //@ decreasing j + 1;\n" +
				"                   while (r < A[j]) {\n" +
				"                         j--;\n" +
				"                   }\n" +
				"\n" +
				"                   //@ assert A[j] <= r & r <=  A[i];\n" +
				"                   if (i <= j) {\n" +
				"                      w = a[i];\n" +
				"                      a[i] = a[j];\n" +
				"                      a[j] = w;\n" +
				"                      //@ assert exchange(A, A_, i, j);\n" +
				"                      //@ assert A[i] <= r & r <= A[j];\n" +
				"                      i ++;\n" +
				"                      j --;\n" +
				"                   }\n" +
				"             }\n" +
				"             if (f <= j) {\n" +
				"                n = j;\n" +
				"             } else if (i <= f) {\n" +
				"                m = i;\n" +
				"             } else {\n" +
				"                n = f;\n" +
				"                m = f;\n" +
				"             }\n" +
				"       }\n" +
				"   }\n" +
				"}\n" 
				},
				"");
	}

}