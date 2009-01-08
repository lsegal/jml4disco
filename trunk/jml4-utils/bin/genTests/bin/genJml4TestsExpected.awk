function removeDirectory(filename,    retVal, c) {
   c = split(filename, retVal, "/")
   return retVal[c]
}
function stripFilename(filename,    retVal) {
   split(filename, retVal, ".")
   return retVal[1]
}
function escapeChar(c) {
   if (c == "\"") return ("\\" c);
   return c
}
function escapeLine(line,    retVal) {
   retVal = ""
   len = length(line)
   for (i=1; i<=len; i++) {
      retVal = retVal escapeChar(substr(line, i, 1))
   }
   return retVal;
}
BEGIN { fn = "_" 
	second = 0
      }

{ first = 0 }
(FILENAME == "_") { print "no file to process" }
(second == 0 && FNR == 1)  { 
	      first  = 1
	      second = 1
	      fn = removeDirectory(FILENAME)
              printf("    public void test_%s() {\n", stripFilename(fn))
              printf("        this.runNegativeTest(\n")
              printf("            new String[] {\n")
              printf("                \"%s\",\n", fn) 
}
(first == 0 && second == 1 && FNR == 1)  { 
	      second = 2
              printf("                \"\"\n") 
              printf("            }\n")
}
(second == 1 && fn != "_") { 
	      printf("                \"%s\\n\" +\n", escapeLine($0)) 
}
(second == 2 && fn != "_") { 
	      printf("            \"%s\\n\" +\n", escapeLine($0)) 
}
END {         printf("            \"\"\n") 
              printf("        );\n")
              printf("    }\n")
    }
