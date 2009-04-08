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
      }

(FILENAME == "_") { print "no file to process" }
(FNR == 1)  { fn = removeDirectory(FILENAME)
              printf("    public void test_%s() {\n", stripFilename(fn))
              printf("        this.runConformTest(\n")
              printf("            new String[] {\n")
              printf("                \"%s\",\n", fn) 
	    }
(fn != "_") { printf("                \"%s\\n\" +\n", escapeLine($0)) 
	    }
END {         printf("                \"\"\n") 
              printf("            });\n")
              printf("    }\n")
    }
