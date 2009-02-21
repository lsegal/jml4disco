package org.jmlspecs.eclipse.jdt.core.tests.esc.casestudy;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class QueensTests extends AbstractRegressionTest {
    public QueensTests(String name) {
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

	private final String testsPath = "tests" + '\\' + "esc" + '\\';
	
    public void test_0001_nQueens() {
        this.runNegativeTest(new String[] {
        		testsPath + "Queens1.java",
				"package tests.esc;\n" +
                "/**\n" +
					" * \n" +
					" * A Java translation of a case study by Jean-Christophe Filli^atre.\n" +
					" * \"Queens on a Chessboard: an Exercise in Program Verification\"\n" +
					" *\n" +
					" * original obfuscated C program:\n" +
					" * t(a,b,c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(\n" +
					" * c+d)/2));return f;}main(q){scanf(\"%d\",&q);printf(\"%d\n\",t(~(~0<<q),0,0));}\n" +
					" */\n" +
					"public class Queens {\n" +
					"\n" +
					"	/**\n" +
					"	 * outputs the number of solutions to the n Queens problem for each of the \n" +
					"	 * entries in args.\n" +
					"	 *  \n" +
					"	 * @param args integers that give the sizes of the board.\n" +
					"	 *             if committed, defaults to 8\n" +
					"	 *             if any entry is non-integer, it is skipped. \n" +
					"	 */\n" +
					"	public static void main(String[] args) {\n" +
					"		if (args.length == 0)\n" +
					"			System.out.println(\"\" + 8 + \" - \" + queens(8));\n" +
					"		for (int i=0; i<args.length; i++) {\n" +
					"			try {\n" +
					"				int n = Integer.parseInt(args[i]);\n" +
					"				int s = queens(n);\n" +
					"				System.out.println(\"\" + n + \" - \" + s);\n" +
					"			} catch (NumberFormatException e) {\n" +
					"				/* ignored */\n" +
					"			}\n" +
					"		}\n" +
					"	}\n" +
					"\n" +
					"	\n" +
					"	/*@  ghost int N;\n" +
					"	  @  ghost int[] col;\n" +
					"	  @  ghost int k;\n" +
					"	  @  ghost int[][] sol;\n" +
					"	  @  ghost int s;\n" +
					"	  @*/\n" +
					"	\n" +
					"	/*@\n" +
					"	  @ ensures \\result == (\\forall int i; i<=i && i < k;\n" +
					"	  @                                    0 <= s[i] && s[i] < N \n" +
					"	  @                   && (\\forall int j; 0 <=j && j < i;\n" +
					"	  @                                      s[i] != s[j] \n" +
					"	  @                                   && s[i] - s[j] != i-j \n" +
					"	  @                                   && s[i] - s[j] != j-i));\n" +
					"	  @ boolean partial_solution(int k, int[] s) {\n" +
					"	       return false;\n" +
					"	   }\n" +
					"	  @*/ \n" +
					"	\n" +
					"	/*@ ensures \\result == (\\forall int k; 0 <= k && k < i; t[k] == u[k]);\n" +
					"	  @\n" +
					"	  @ boolean solution(int[] s) {\n" +
					"	      return partial_solution(N, s);\n" +
					"	   }\n" +
					"	  @*/	\n" +
					"\n" +
					"	  /*@ ensures \\result == (\\forall int k; 0 <= k && k < i; t[k] == u[k]);\n" +
					"	    @ boolean eq_prefix(int[] t, int[] u, int i) {\n" +
					"	        return (\\forall int k; 0 <= k && k < i; t[k] == u[k]);\n" +
					"	     }\n" +
					"	    @*/\n" +
					"	  \n" +
					"	/*@ ensures \\result == eq_prefix(t, u, N);\n" +
					"	  @ boolean eq_sol(int[] t, int[] u) {\n" +
					"	  @    return eq_prefix(t, u, N);\n" +
					"	  @ }\n" +
					"	  @*/\n" +
					"	\n" +
					"	/*@ ensures \\result == (\\exists int i; 0 <= i && i < N; eq_prefix(s1, s2, i) && s1[i] < s2[i]);\n" +
					"	  @ boolean lt_sol(int[] s1, int[] s2) {return false;}\n" +
					"	  @*/\n" +
					"\n" +
					"	/*@\n" +
					"	  @ ensures \\result == (\\forall int i, j; a <= i && i < j && j < b;\n" +
					"	  @                                       lt_sol(s[i], s[j]); \n" +
					"	  @ boolean isSorted(int[][] s, int a, int b) {return false; }\n" +
					"	  @*/\n" +
					"	\n" +
					"	/*@ requires n == N & s == 0 & k == 0;\n" +
					"	  @ ensures  \\result == s;\n" +
					"	  @ ensures  isSorted(sol, 0, s); \n" +
					"	  @ ensures  (\\forall t; solution(t) <==> (\\exists int i; 0 <= i && i < \\result; \n" +
					"	  @                                                       eq_sol(t, sol[i]))); \n" +
					"	  @*/\n" +
					"	public static int queens(int n) {\n" +
					"		return t(~(~0<<n), 0, 0);\n" +
					"	}\n" +
					"	\n" +
					"	/*@ requires 0 <= k;\n" +
					"	  @ requires k + card(iset(a)) == N();\n" +
					"	  @ requires 0 <= s;\n" +
					"	  @ requires (\\forall int i; in_(i, iset(a)) <==> (0<= i & i <= N() && \\forall int j; 0<= j & j < k; i != col[j]));\n" +
					"	  @ requires (\\forall int i; i >= 0; (in_(i, iset(b)) <==> (\\exists int j; 0<= j & j < k; col[j] == i + j - k));\n" +
					"	  @ requires (\\forall int i; i >= 0; (in_(i, iset(c)) <==> (\\exists int j; 0<= j & j < k; col[j] == i + k - j));\n" +
					"	  @ requires partial_solution(k, col);\n" +
					"	  @ modifies col[k..], s,k, sol[s..][..];\n" +
					"	  @ ensures \\result == s - \\old(s);\n" +
					"	  @ ensures \\result >= 0;\n" +
					"	  @ ensures k == \\old(k);\n" +
					"	  @ ensures sorted(sol, \\old(s), s);\n" +
					"	  @ ensures (\\forall int[] t; ((solution(t) && eq_prefix(col,t,k)) <==>\n" +
					"                   \\exists int i; \\old(s) <= i && i < s && eq_sol(t, sol[i])));\n" +
					"	  @*/\n" +
					"	private static int t(int a, int b, int c) {\n" +
					"		int d;\n" +
					"		int e = a & ~b & ~c;\n" +
					"		int f = 1;\n" +
					"		int e_ = e;\n" +
					"		if (a != 0) {\n" +
					"           // maintaining included(iset(e), iset(e_))\n" +
					"           // maintaining included(iset(e), iset(e_))\n" +
					"			for (f = 0; (d = e & -e) != 0; e -= d) {\n" +
					"				f += t(a-d, (b+d)*2, (c+d)/2);\n" +
					"			}\n" +
					"		}\n" +
					"		return f;\n" +
					"	}\n" +
					"\n" +
					"}\n"
                },
                "----------\n" +
        		"1. ERROR in tests\\esc\\Queens1.java (at line 10)\n" + 
        		"	//@ assert isDivisor(10, 3);\n" + 
        		"	           ^^^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n");
    }

}

