# File: Makefile
#
# $Id$
#
# Copyright (C) 2007, DSRG, dsrg.org.
#
#------------------------------------------------------------------------------

TOP_DIR=../..

default: defs-info default0 

include $(TOP_DIR)/bin/Makefile.defs

JIKESPG?=jikespg
WEAVER?=../../bin/weaveParserFiles.pl
DTU?=$(TOP_DIR)/bin/dtu.pl

LOCAL_BUILD_DIR=./build
FILES_TO_RM=build *.class *~ *.tmp *-log.txt *.bak

#------------------------------------------------------------------------------

.PHONY: clean compile-and-run fix-readableNames-properties copy-to-dest
.PHONY: weaveParserSource updateParserFiles
.PHONY: step1 step2

default0:
	@echo "What do you want to do? To rebuild the parser:"
	@echo " - $(MAKE) step1"
	@echo " - Then in eclipse, refresh your JDT core project"
	@echo " - $(MAKE) step2"
	@echo " - Then in eclipse, refresh your JDT core project"
	@echo " WARNING: it is crucial that step1 be followed by a rebuild in Eclipse"
	@echo "          of the JDT _before_ doing step 2."

#------------------------------------------------------------------------------
# Step1:

step1: clean weaveParserSource

FILES_TO_REBUILD0=prefix-Parser.java prefix-ParserBasicInformation.java prefix-TerminalTokens.java
FILES_TO_REBUILD_IN_LOCAL_DIR=$(subst prefix-, $(LOCAL_BUILD_DIR)/,$(FILES_TO_REBUILD0))
FILES_TO_REBUILD_AT_SRC=$(subst prefix-, $(PARSER_DIR)/,$(FILES_TO_REBUILD0))

weaveParserSource: $(LOCAL_BUILD_DIR)
	-cp -f $(GRAMMAR_DIR)/java.g $(LOCAL_BUILD_DIR)
	# Convert EOL from DOS to Unix format ...
	$(DTU) $(LOCAL_BUILD_DIR)/java.g
	-cp -f $(FILES_TO_REBUILD_AT_SRC) $(LOCAL_BUILD_DIR)
	cd $(LOCAL_BUILD_DIR) && $(JIKESPG) java.g > jikespg-log.txt
	@echo "==========================================================="
	@-grep "This grammar" $(LOCAL_BUILD_DIR)/jikespg-log.txt
	@-grep "Number of .* conflicts:" $(LOCAL_BUILD_DIR)/jikespg-log.txt
	@echo "==========================================================="
	chmod a+r $(LOCAL_BUILD_DIR)/*
	$(WEAVER) -d $(LOCAL_BUILD_DIR)
	-cp -f $(FILES_TO_REBUILD_IN_LOCAL_DIR) $(PARSER_DIR)

$(LOCAL_BUILD_DIR):
	mkdir $(LOCAL_BUILD_DIR)

#------------------------------------------------------------------------------
# Step2:

step2: updateParserFiles2
updateParserFiles2: compile-and-run fix-readableNames-properties copy-to-dest

CP0=$(ECLIPSE_WORKSPACE)/org.eclipse.jdt.core/bin/:.
CP=$(call canonicalize,$(CP0))

PARSER_RSC_AND_PROP_FILES=*.rsc readableNames.properties
# The paths in the following list do not need to be in canonical form
# because they are being passed as arguments to $(JAVA).
UPF_FILES=javadcl.java javahdr.java

compile-and-run:
	$(JAVAC) -source 1.4 -classpath $(CP) -d $(LOCAL_BUILD_DIR) UpdateParserFiles.java
	cd "$(LOCAL_BUILD_DIR)" && \
		$(JAVA) -classpath $(CP) UpdateParserFiles $(UPF_FILES) > UpdateParserFiles-log.txt

copy-to-dest:
	-cd "$(LOCAL_BUILD_DIR)" && \
		cp -f $(PARSER_RSC_AND_PROP_FILES) $(PARSER_DIR)
	-cd "$(LOCAL_BUILD_DIR)" && \
		cp -f $(PARSER_RSC_AND_PROP_FILES) $(PARSER_BIN_DIR)
# ... copying to the bin directory should be unnecessary (since Eclipse will do it on a refresh?)

fix-readableNames-properties:
	-mv $(LOCAL_BUILD_DIR)/readableNames.properties $(LOCAL_BUILD_DIR)/readableNames.properties.tmp
	-cat readableNames-properties-header.txt $(LOCAL_BUILD_DIR)/readableNames.properties.tmp \
		> $(LOCAL_BUILD_DIR)/readableNames.properties

clean:
	@echo "Removing local temporary and generated files."
	@-rm -Rf $(FILES_TO_RM)

#------------------------------------------------------------------------------
# End of file
