PKG = Mathlib

PLUGINOUT = build/plugin
LIBMATHLIBPLUGIN = $(PLUGINOUT)/Mathlib_Plugin.so

PLUGINSRCS=$(shell mkdir -p build/Mathlib; env LEAN_PATH=build: bash ./rec_deps.sh Mathlib/Plugin.lean)

ifdef BUILD_PLUGIN
include lean.mk
LEANC_OPTS += -fPIC

$(LIBMATHLIBPLUGIN): $(addprefix $(TEMP_OUT)/,$(PLUGINSRCS:.lean=.o))
	leanc -shared -o $@ -x none $^

else

MORE_DEPS = $(LIBMATHLIBPLUGIN)
include lean.mk
LEAN_OPTS += --plugin=$(LIBMATHLIBPLUGIN)

$(LIBMATHLIBPLUGIN): $(PLUGINSRCS)
	$(MAKE) BUILD_PLUGIN=1 OUT=$(PLUGINOUT) $(LIBMATHLIBPLUGIN) LEAN_PATH=:$(PLUGINOUT)

endif
