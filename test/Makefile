# Copyright (c) Microsoft Corporation.  All rights reserved.
#
# Given a TAG (an output directory name) and a set of directories (DIR),
# run T2 on all .c and .t2 files found recursively in DIR
# and place log files into TAG and then create a summary csv file.
#
# Example use:
#   $ make TAG=RUN_12Oct2012 DIR=known instr/unit
#

## -----------------------------------------------------------------------------
#  Makefile parameters
## -----------------------------------------------------------------------------

# Give a TAG
# All output files are placed inside $(TAG)/
ifeq ("$(MAKECMDGOALS)", "")
ifndef TAG
$(error Must give TAG=<string> -- try make help)
endif
endif

# Directories to search inside for .t2 and .c files
DIR ?= known

# Passed through to wlimit
TIMEOUT ?= 100# seconds
MEMOUT  ?= 2500# megabytes

# Top-level where T2 is checked-out
SRC ?= $(shell cygpath -t unix ~/sd/) 
SRCUNIX = $(shell cygpath -t unix $(SRC))
SRCWIN = $(shell cygpath -t mixed $(SRC))

# Specify these so we know where to pick up T2
T2BRANCH ?= src
T2BUILD  ?= Debug

# Give extra arguments to T2 
# Be careful that these don't clash with the hard-coded ones below
T2ARGS   ?=

# Be chatty
ifdef VERBOSE
V =
else
V ?= @
endif

## -----------------------------------------------------------------------------
#  Everyone else should work from here on down
## -----------------------------------------------------------------------------

# Where to pick up T2 (absolute unix path)
PICKUP_T2EXE:=$(SRCUNIX)/$(T2BRANCH)/bin/$(T2BUILD)/T2.exe

# Where to place output and copies of binaries
OUTDIR:=$(shell cygpath -t unix `pwd`)/$(TAG)
BINDIR:=$(OUTDIR)/bin

# Executables (unix paths)
WLIMITEXE:=$(SRCUNIX)/test/tools/wlimit.exe
GATHEREXE:=$(SRCUNIX)/test/tools/gather_results
T2EXE:=$(BINDIR)/T2.exe
# windows paths for T2 and slayer
T2EXE_WIN:=$(shell cygpath -t mixed $(T2EXE))

# Command arguments
WLIMIT_ARGS=/r /w $(TIMEOUT) /m $(MEMOUT)
COMMON_ARGS=-termination
TFILE_ARGS=$(COMMON_ARGS) $(T2ARGS) \
           -input_t2

# Running T2
# $1 = extra command arguments
# $2 = input file
# $3 = output file
# append true at the end so that we always return with exit code 0
t2cmd = $(WLIMITEXE) $(WLIMIT_ARGS) \
        $(T2EXE_WIN) $(1) $(2) &> $(3) || true

# Input files minus exclude files
TSRC:=$(shell find $(DIR) -name "*.t2")
ifdef EXCLUDE_FILE
EXCLUDES:=$(shell cat $(EXCLUDE_FILE))
TSRC:=$(filter-out $(EXCLUDES),$(TSRC))
endif

# Output files
# NC: nameclash problem if there is a file.c and file.t2 in the same directory
TOUT:=$(TSRC:%.t2=$(OUTDIR)/%.t2.out)

default: $(OUTDIR) $(BINDIR) \
         $(WLIMITEXE) \
         $(TOUT) \
         $(OUTDIR)/RESULT.csv

# Create new output directory if it doesn't already exist
$(OUTDIR):
	$(V) test -d $@ || mkdir $@
	@echo "Generated on `date`"                                       > $@/INFO
	@echo                                                            >> $@/INFO
	@echo "TIMEOUT  : $(TIMEOUT)"                                    >> $@/INFO
	@echo "MEMOUT   : $(MEMOUT)"                                     >> $@/INFO
	@echo                                                            >> $@/INFO
	@echo "T2 from  : $(PICKUP_T2EXE)"                               >> $@/INFO
	@echo ".t2 args : $(TFILE_ARGS)"                                 >> $@/INFO
	@echo                                                            >> $@/INFO
	@echo "t2 cmd   : $(call t2cmd,$(TFILE_ARGS),'f.t2','f.t2.out')" >> $@/INFO

# Copy across binaries
$(BINDIR): $(OUTDIR)
	$(V) echo $(BINDIR)
	$(V) test -d $@ || mkdir $@

$(T2EXE): $(PICKUP_T2EXE) | $(BINDIR)
	$(V) echo $(T2EXE)
	$(V) test -e $@ || cp -a $(<D)/* $(OUTDIR)/bin

$(TOUT) : $(OUTDIR)/%.t2.out : %.t2 $(T2EXE)
	@echo $<
	$(V) test -d $(@D) || mkdir -p $(@D)
	$(V) $(call t2cmd,$(TFILE_ARGS),$<,$@)

# Gather results
$(GATHEREXE): gather_results.ml
	$(V) ocamlc unix.cma str.cma $< -o gather_results

$(OUTDIR)/RESULT.csv: $(TOUT) $(GATHEREXE)
ifdef EXPECTED_FILE
	$(V) $(GATHEREXE) -expected $(EXPECTED_FILE) $(OUTDIR)
else
	$(V) $(GATHEREXE) $(OUTDIR)
endif

# Unit tests for T2
.PHONY: unit
unit: $(T2EXE)
	$(V) $(SRCUNIX)/$(T2EXE) -tests -stats

.PHONY: clean
clean:
# *** Very important to protect this 'rm' ***
# If a tag is not given then $(OUTDIR) is the top-level test dir!
ifdef TAG
	$(V) rm -rf $(OUTDIR)
endif
	$(V) find $(DIR) -regex ".*rawcfgf\|.*li\|.*dot" -delete

.PHONY: help
help:
	@echo "Usage: make TAG=<string> [options]"
	@echo
	@echo "Run tests and place resulting output in TAG"
	@echo
	@echo "Options can be:"
	@echo "  DIR=d1 d2 ... dn    -- a list of directories with tests to run"
	@echo "                      -- default is $(DIR)"
	@echo "  TIMEOUT=n           -- timeout in seconds (default: $(TIMEOUT))"
	@echo "  MEMOUT=n            -- memout in memgabytes (default: $(MEMOUT))"
	@echo "  EXCLUDE_FILE=f      -- file containing tests to omit from the run"
	@echo
	@echo "  T2ARGS=...          -- extra arguments for T2"
	@echo
	@echo "  SRC=...             -- top-level local SD checkout (default: $(SRC))"
	@echo
	@echo "  T2BRANCH=...        -- T2 branch to use (default: $(T2BRANCH))"
	@echo "  T2BUILD=...         -- T2 build to use (default: $(T2BUILD))"
	@echo
	@echo "  VERBOSE=1           -- print out make commands"
	@echo
	@echo "make TAG=<string> clean"
	@echo "Will delete the TAG directory and any temporary files"
