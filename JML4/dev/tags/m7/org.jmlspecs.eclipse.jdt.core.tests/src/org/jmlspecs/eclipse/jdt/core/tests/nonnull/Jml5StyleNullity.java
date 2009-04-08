package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.io.File;
import java.io.IOException;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlCoreTestsUtil;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlTestCase;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class Jml5StyleNullity extends JmlTestCase{
	
	public final String workspace = "..";
	public final String path2jml4annotations = workspace + "/org.jmlspecs.annotation/bin";
	
	public Jml5StyleNullity(String name) {
		super(name);
	}
	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = path2jml4annotations;
        return defaultClassPaths;
   }	
	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();
	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportJmlCommentDisabled, CompilerOptions.ERROR);
		options.put(JmlCompilerOptions.OPTION_SpecPath, Jml5StyleNullity.getSpecPath());
        options.put(JmlCompilerOptions.OPTION_Compliance, JmlCompilerOptions.VERSION_1_5);
        options.put(JmlCompilerOptions.OPTION_Source, JmlCompilerOptions.VERSION_1_5);
        options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);		
	    return options;
	}
	 /*package*/ static String getSpecPath() {
			String fileSeparator = System.getProperty("file.separator"); // /
			String pathSeparator = System.getProperty("path.separator"); // :
			// String user = System.getProperty("user.name");
			// String JML2_ROOT = System.getProperty("jml2.root");
			// String JML2specs = fileSeparator + "home" + fileSeparator + user + fileSeparator + "dev" + fileSeparator + "JML2" + fileSeparator + "specs";
			String sp = "." + pathSeparator 
				+ "." + fileSeparator + "specs" + pathSeparator
				+ "." + fileSeparator + "src" + pathSeparator;
				// + JML2specs;
			return sp;
	    }	
	public void test_0001_NullityAnnotationDuplicate() {
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	//FIELDS \n"+
				"  @Nullable @Nullable String able1 = null;\n" +
				"  @Nullable /*@nullable*/ String able2 = null;\n" +
				"  @Nullable /*@non_null*/ String able3 = null;\n" +
				"  @Nullable /*@non_null*/ String able4 = \"test\";\n" +
				"  @NonNull @NonNull String non1 = null;\n" +
				"  @NonNull /*@nullable*/ String non2 = null;\n" +
				"  @NonNull /*@non_null*/ String non3 = null;\n" +
				"  @NonNull /*@non_null*/ String non4 = \"test\";\n" +				
				"	//CONSTRUCTORS \n"+
				"  X(@Nullable @Nullable String s) {s = null;}\n" +
				"  X(@NonNull @NonNull Object o) {o = null;}\n" +
				"	//METHOD PARAMETERS \n"+
				"  void m1(@Nullable @Nullable String s) {\n s = null;\n}\n" +
				"  void m2(@Nullable /*@nullable*/ String s) {\n s = null;\n}\n" +
				"  void m3(@Nullable /*@non_null*/ String s) {\n s = null;\n}\n" +
				"  void m4(@Nullable /*@non_null*/ String s) {\n s = \"test\";\n}\n" +
				"  void m5(@NonNull @NonNull String s) {\n s = null;\n}\n" +	
				"  void m6(@NonNull /*@nullable*/ String s) {\n s = null;\n}\n" +
				"  void m7(@NonNull /*@non_null*/ String s) {\n s = null;\n}\n" +
				"  void m8(@NonNull /*@non_null*/ String s) {\n s = \"test\";\n}\n" +
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	@Nullable @Nullable String able1 = null;\n" + 
				"	^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 4)\n" + 
				"	@Nullable @Nullable String able1 = null;\n" + 
				"	          ^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 8)\n" + 
				"	@NonNull @NonNull String non1 = null;\n" + 
				"	^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 8)\n" + 
				"	@NonNull @NonNull String non1 = null;\n" + 
				"	         ^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 13)\n" + 
				"	X(@Nullable @Nullable String s) {s = null;}\n" + 
				"	  ^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 13)\n" + 
				"	X(@Nullable @Nullable String s) {s = null;}\n" + 
				"	            ^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 14)\n" + 
				"	X(@NonNull @NonNull Object o) {o = null;}\n" + 
				"	  ^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 14)\n" + 
				"	X(@NonNull @NonNull Object o) {o = null;}\n" + 
				"	           ^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 16)\n" + 
				"	void m1(@Nullable @Nullable String s) {\n" + 
				"	        ^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"10. ERROR in X.java (at line 16)\n" + 
				"	void m1(@Nullable @Nullable String s) {\n" + 
				"	                  ^^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @Nullable\n" + 
				"----------\n" + 
				"11. ERROR in X.java (at line 28)\n" + 
				"	void m5(@NonNull @NonNull String s) {\n" + 
				"	        ^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n" + 
				"12. ERROR in X.java (at line 28)\n" + 
				"	void m5(@NonNull @NonNull String s) {\n" + 
				"	                 ^^^^^^^^\n" + 
				"[@cat:type] Duplicate annotation @NonNull\n" + 
				"----------\n",null, true, options, true, true, true);
    }	
	public void test_0002_MethodArgument_Nullity() {
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"  void m1(@Nullable String s) {s = null;}\n" +				
				"  void m2(@Nullable String s) {s = \"test\";}\n" +			
				"  void m3(@NonNull String s) {s = null;}\n" +				
				"  void m4(@NonNull String s) {s = \"test\";}\n" +			
				"  void m5(@NonNull String s, @Nullable Object o) {\n" + 	
				"   s = null;\n" +
				"   o = null;\n" +
				"  }\n" + 				
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 5)\n" + 
				"	void m3(@NonNull String s) {s = null;}\n" + 
				"	                            ^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 8)\n" + 
				"	s = null;\n" + 
				"	^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n",null, true, options, true, true, true);
	}	
	public void test_0003_MethodReturn_NullityAnnotation() {
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	@Nullable String m1() { return null;}\n" +
				"	@Nullable String m2() { return \"test\";}\n" +
				"	@NonNull String m3() { return null;}\n" +
				"	@NonNull String m4() { return \"test\";}\n" +
				"	@Nullable String m5(@Nullable String s) { return s;}\n" +
				"	@Nullable String m6(@NonNull String s) { return s;}\n" +
				"	@NonNull String m7(@Nullable String s) { return s;}\n" +
				"	@NonNull String m8(@NonNull String s) { return s;}\n" +					
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 5)\n" + 
				"	@NonNull String m3() { return null;}\n" + 
				"	                       ^^^^^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] The method must return a non-null result\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 9)\n" + 
				"	@NonNull String m7(@Nullable String s) { return s;}\n" + 
				"	                                         ^^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] The method must return a non-null result\n" + 
				"----------\n",null, true, options, true, true, true);
    }	
	public void test_0004_ConstructorArgument_NullityAnnotation() {
		Map<String, String> options = getCompilerOptions();
        options.put(JmlCompilerOptions.OPTION_Compliance, JmlCompilerOptions.VERSION_1_5);
        options.put(JmlCompilerOptions.OPTION_Source, JmlCompilerOptions.VERSION_1_5);
        options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	X(@Nullable String able, @NonNull String non) { }\n" + 
				"	void m1(){ X x = new X(null,null); }\n" +
				"	void m2(){ X x = new X(\"test\",\"test\"); }\n" +
				"	void m3(){ X x = new X(null,\"test\"); }\n" +
				"	void m4(){ X x = new X(\"test\",null); }\n" +
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	void m1(){ X x = new X(null,null); }\n" + 
				"	                 ^^^^^^^^^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possibly null actual parameter cannot be assigned to non_null formal parameter 2, non\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 7)\n" + 
				"	void m4(){ X x = new X(\"test\",null); }\n" + 
				"	                 ^^^^^^^^^^^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possibly null actual parameter cannot be assigned to non_null formal parameter 2, non\n" + 
				"----------\n",null, true, options, true, true, true);
    }		
	public void test_0005_ConstructorParameter_NullityAnnotation() {
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	X(@NonNull String s) {}\n" + 
				"	void m() { X x = new X(null);}\n" +
				"	void m1(){ X x = new X(\"test\");}\n" +
				"	void m2(){ String s; X x = new X(s);}\n" +
				"	void m3(){ @Nullable String s; X x = new X(s);}\n" +
				"	void m4(){ @Nullable String s=\"test\"; X x = new X(s);}\n" +
				"	void m5(){ @NonNull String s; X x = new X(s);}\n" +
				"	void m6(){ @NonNull String s=\"test\"; X x = new X(s);}\n" +
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	void m() { X x = new X(null);}\n" + 
				"	                 ^^^^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 6)\n" + 
				"	void m2(){ String s; X x = new X(s);}\n" + 
				"	                           ^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 6)\n" + 
				"	void m2(){ String s; X x = new X(s);}\n" + 
				"	                                 ^\n" + 
				"[@cat:internal] The local variable s may not have been initialized\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 7)\n" + 
				"	void m3(){ @Nullable String s; X x = new X(s);}\n" + 
				"	                                     ^^^^^^^^\n" + 
				"[@cat:type] [@sup:nnts] Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 7)\n" + 
				"	void m3(){ @Nullable String s; X x = new X(s);}\n" + 
				"	                                           ^\n" + 
				"[@cat:internal] The local variable s may not have been initialized\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 9)\n" + 
				"	void m5(){ @NonNull String s; X x = new X(s);}\n" + 
				"	                                          ^\n" + 
				"[@cat:internal] The local variable s may not have been initialized\n" + 
				"----------\n",null, true, options, true, true, true);
	}
	public void test_0006_Field_NullityAnnotation(){
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	@Nullable String able1 = null ; \n" +
				"	@Nullable String able2 = \"test\"; \n" +
				"	@NonNull String non1 = null; \n" +
				"	@NonNull String non2 = \"test\";\n" +			
				"}"},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	@NonNull String non1 = null; \n"+
				"	                ^^^^\n"+
				"[@cat:type] [@sup:nnts] Possible assignment of null to an L-value declared non_null\n"+
				"----------\n",null, true, options, true, true, true);
	}
	public void test_0007_Local_NullityAnnotation(){
		Map<String, String> options = getCompilerOptions();
		this.runNegativeTest(
			new String[] {
				"X.java",
				"import org.jmlspecs.annotation.*;\n" +
				"class X {\n" +
				"	void m() { \n" +
				"		@Nullable String able1 = null ; \n" +
				"		@Nullable String able2 = \"test\"; \n" +
				"		@NonNull  String non1 = null; \n" +
				"		@NonNull  String non2 = \"test\";\n" +
				"	}\n" +
				"}"},
				"----------\n"+
				"1. ERROR in X.java (at line 6)\n"+
				"	@NonNull  String non1 = null; \n"+
				"	                 ^^^^\n"+
				"[@cat:type] [@sup:nnts] Possible assignment of null to an L-value declared non_null\n"+
				"----------\n",null, true, options, true, true, true);
	}

    public void test_1000_Persistence() throws IOException {
    	String batchCompilerOptions = "-jml -source 1.5 -target 1.5 -rac -dbc -warn:+nnts -nullable";
    	String classPath= path2jml4annotations + File.pathSeparator;
		String source_Helper = 
			"package a;\n" +
			"import org.jmlspecs.annotation.*;\n" +
			"public class Helper {\n" +
			"		public static @NonNull String able = \"test\"; \n" +
			"}\n";
		String helperPath = "a" + File.separator + "Helper" + JmlCoreTestsUtil.defaultJavaExtension();
		
		String source_X =
			"package b;\n" +
			"public class X {\n" +
			"	/*@non_null*/ String s = a.Helper.able;\n" +
			"}\n";
		String xPath = "b" + File.separator + "X" + JmlCoreTestsUtil.defaultJavaExtension();
		String[] pathAndContents = new String[] {
				helperPath,
				source_Helper,
				xPath,
				source_X,
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.;
		String result;
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + helperPath, srcPath, destDir, classPath);
		//Delete Helper.java file
		boolean b = new File(SOURCE_DIRECTORY + File.separator + helperPath).delete();
		String expected = "";
		assertEquals(helperPath, "", result);
		System.setProperty("jdt.compiler.useSingleThread", "true");
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir, classPath);
		expected = "----------\n"+
					"1. WARNING in "+ destDir + File.separator+ xPath + " (at line 3)\n"+
					"	/*@non_null*/ String s = a.Helper.able;\n"+
		            "	                     ^\n"+
		            "Possible assignment of null to an L-value declared non_null\n"+
		            "----------\n"+
		            "1 problem (1 warning)";
		assertEquals(xPath + ": " + result, expected, result); 
	}
}

