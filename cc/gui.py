#!/usr/bin/python3

import os
from os import listdir
from os.path import isfile, join
import gi
gi.require_version('Gtk', '3.0')
from gi.repository import Gtk, Gdk
import subprocess
import networkx as nx
import utils
import shutil
import pomset
from ccpom import *
from diff import run_diff

class Workspace():
    def __init__(self, sgg_path):
        self.sgg_absolute_path = sgg_path
        self.semantics = None
        self.cc2 = None
        self.cc3 = None
        self.projections = None

    def get_root_folder(self):
        return os.path.dirname(self.sgg_absolute_path)
    
    def gen_choreography_graphml(self):
        os.system("../gg2gml %s > %s" % (
            self.sgg_absolute_path,
            self.get_root_folder() + "/choreography.graphml"
        ))

    def get_choreography_png_path(self):
        return self.get_root_folder() + "/choreography.png"
    
    def gen_choreography_png(self):
        self.gen_choreography_graphml()
        os.system("../chor2dot -d %s/ -fmt sloppygml %s/choreography.graphml" % (
            self.get_root_folder(), 
            self.get_root_folder()
        ))
        os.system('dot -Tpng %s/choreography.dot -o %s' % (
            self.get_root_folder(),
            self.get_choreography_png_path())
        )

    def get_semantics_folder(self):
        return self.sgg_absolute_path.split(".")[0]

    def list_files_in_folder(self, folder):
        files = [f for f in listdir(folder) if isfile(join(folder, f))]
        return files

    def get_semantics_png_path(self, f):
        return self.get_semantics_folder() + "/%s.png" % f


    def delete_folder(self, folder):
        try:
            shutil.rmtree(folder)
        except:
            pass
    
    def gen_semantics(self):
        # I should ensure this goes in the third position and remove all the past semantics from the tree
        self.delete_folder(self.get_semantics_folder())
        cmd = "../gg2pom -d %s/ --gml %s" % (
            self.get_root_folder(), 
            self.sgg_absolute_path
        )
        os.system(cmd)
        self.semantics = {}
        for f in self.list_files_in_folder(self.get_semantics_folder()):
            graph = nx.readwrite.graphml.read_graphml(join(self.get_semantics_folder(), f))
            self.semantics[f] = graph
            utils.debug_pomset(graph, join(self.get_semantics_folder(), f))

    def get_cc2_folder(self):
        return self.get_root_folder() + "/cc2"
    
    def gen_cc2(self):
        if self.semantics is None:
            return
        self.delete_folder(self.get_cc2_folder())
        os.makedirs(join(self.get_cc2_folder(),  "closure"))
        os.makedirs(join(self.get_cc2_folder(),  "synthesis"))
        
        pomsets = [self.semantics[f] for f in self.semantics]
        cc2c = cc2closure(pomsets)
        self.cc2 = {"closure": {}, "mapping": {}}
        cc2res = cc2pom(cc2c, pomsets)
        i = 0
        for pm in cc2c:
            # TODO: we should use the transitive reduction, but it does not work
            nx.readwrite.graphml.write_graphml(pm, join(self.get_cc2_folder(),  "closure", "%d.graphml"%i))
            utils.debug_pomset(pm, join(self.get_cc2_folder(),  "closure", "%d"%i))
            self.cc2["closure"][i] = pm
            if not cc2res[i] is None:
                self.cc2["mapping"][i] = cc2res[i]
            i+=1

    def get_cc2_closure_png_path(self, i):
        return join(self.get_cc2_folder(),  "closure", "%d.png"%i)

    def get_cc2_counter_choreography_folder(self, pm_idx):
        return join(self.get_cc2_folder(),  "synthesis", "%d"%pm_idx)
    def get_cc2_counter_choreography_png(self, pm_idx):
        return join(self.get_cc2_counter_choreography_folder(pm_idx), "%d.png"%pm_idx)

    def get_cc3_closure_png_path(self, i):
        return join(self.get_cc3_folder(),  "closure", "%d.png"%i)
    def get_cc3_counter_choreography_folder(self, pm_idx):
        return join(self.get_cc3_folder(),  "synthesis", "%d"%pm_idx)
    def get_cc3_counter_choreography_png(self, pm_idx):
        return join(self.get_cc3_counter_choreography_folder(pm_idx), "%d.png"%pm_idx)

    
    def gen_cc2_choreography(self, pm_idx):
        if self.cc2 is None:
            return
        if not pm_idx in self.cc2["closure"]:
            return
        pm = self.cc2["closure"][pm_idx]
        os.system('../pom2gg -d %s %s' % (
            join(self.get_cc2_folder(),  "synthesis"),
            join(self.get_cc2_folder(),  "closure", "%d.graphml"%pm_idx)
        ))
        os.system('dot -Tpng %s.dot -o %s' % (
            join(self.get_cc2_counter_choreography_folder(pm_idx), "%d"%pm_idx),
            self.get_cc2_counter_choreography_png(pm_idx))
        )

    def get_cc2_diff_path(self, counter_idx, branch_idx):
        return "%s/diff_%d.png" % (self.get_cc2_counter_choreography_folder(counter_idx), branch_idx)

    def gen_cc2_diff(self, pm_idx):
        if self.cc2 is None:
            return
        if not pm_idx in self.cc2["closure"]:
            return
        pm = self.cc2["closure"][pm_idx]
        g1 = nx.readwrite.graphml.read_graphml(self.get_root_folder() + "/choreography.graphml")
        g2 = nx.readwrite.graphml.read_graphml(join(self.get_cc2_folder(),  "synthesis", "%d"%pm_idx, "%d.graphml"%pm_idx))
        res = run_diff(g1, g2, self.get_cc2_counter_choreography_folder(pm_idx))
        for i in res:
            os.system("../chor2dot -d %s/ -fmt gmldiff %s/diff_%d.graphml" % (
                self.get_cc2_counter_choreography_folder(pm_idx), 
                self.get_cc2_counter_choreography_folder(pm_idx),
                i
            ))
            os.system('dot -Tpng %s/diff_%d.dot -o %s' % (
                self.get_cc2_counter_choreography_folder(pm_idx),
                i,
                self.get_cc2_diff_path(pm_idx, i)
            ))
        return res

    def get_cc3_folder(self):
        return self.get_root_folder() + "/cc3"

    # remove closure elements that are prefix of other elements
    def filter_cc3_closure(self, cc3c):
        filtered_closure = []
        nm = iso.categorical_node_match(["subject", "partner", "in", "out"], ["", "", "", ""])
        for pomset in cc3c:
            found = False
            for pomset1 in cc3c:
                if pomset1 == pomset:
                    continue
                prefixes = get_all_prefix_graphs(pomset1, False)
                for pomset2 in prefixes:
                    if (nx.is_isomorphic(pomset, pomset2, node_match=nm)):
                        found = True
                        break
                if found:
                    break
            if not found:
                filtered_closure.append(pomset)
        return filtered_closure

    def fix_cc3_counter_example(self, pom):
        last_int = max([int(x) for x in pom.nodes()])
        for node in list(pom.nodes()):
            if not "out" in pom.node[node]:
                continue
            outs = [b for (a, b) in pom.out_edges(node)]
            found = False
            for node1 in outs:
                if not "in" in pom.node[node1]:
                    continue
                if pom.node[node1]["subject"] == pom.node[node]["partner"] and \
                   pom.node[node]["subject"] == pom.node[node1]["partner"] and \
                   pom.node[node1]["in"] == pom.node[node]["out"]:
                    found = True
                    break
            if not found:
                last_int += 1
                pom.add_node(last_int, **(dict(pomset.get_matching_label(pom.node[node]))))
                pom.add_edge(node, last_int)
        return pom

    def gen_cc3(self):
        if self.semantics is None:
            return
        self.delete_folder(self.get_cc3_folder())
        os.makedirs(join(self.get_cc3_folder(),  "closure"))
        os.makedirs(join(self.get_cc3_folder(),  "synthesis"))
        
        pomsets = [self.semantics[f] for f in self.semantics]
        self.cc3 = {"closure": {}, "mapping": {}}

        (cc3c, prefixes) = cc3closure(pomsets)
        cc3c = self.filter_cc3_closure(cc3c)
        cc3res = cc3pom(cc3c, prefixes)
        i = 0
        for pm in cc3c:
            # TODO: we should use the transitive reduction, but it does not work
            fix_pom_out = self.fix_cc3_counter_example(pm)
            nx.readwrite.graphml.write_graphml(fix_pom_out, join(self.get_cc3_folder(),  "closure", "%d.graphml"%i))
            utils.debug_pomset(fix_pom_out, join(self.get_cc3_folder(),  "closure", "%d"%i))
            self.cc3["closure"][i] = fix_pom_out
            if not cc3res[i] is None:
                self.cc3["mapping"][i] = cc3res[i]
            i+=1


UI_INFO = """
<ui>
  <menubar name='MenuBar'>
    <menu action='FileMenu'>
      <menuitem action='FileOpenChoreography' />
      <menu action='FileNew'>
        <menuitem action='FileNewStandard' />
        <menuitem action='FileNewFoo' />
        <menuitem action='FileNewGoo' />
      </menu>
      <separator />
      <menuitem action='FileGenSemantics' />
      <separator />
      <menuitem action='CC2' />
      <menuitem action='CC3' />
      <menuitem action='pom2sgg' />
      <menuitem action='sgg2diff' />
      <separator />
      <menuitem action='FileQuit' />
    </menu>
  </menubar>
  <toolbar name='ToolBar'>
    <toolitem action='FileOpenChoreography' />
    <toolitem action='FileQuit' />
  </toolbar>
</ui>
"""




class MainWindow(Gtk.Window):

    def __init__(self):
        Gtk.Window.__init__(self, title="PomChor 0.99 Beta 2")

        self.workspace = None
        # reverse mapping for tree-vew
        self.tree_mapping = {}
        
        self.set_default_size(600, 400)

        action_group = Gtk.ActionGroup("my_actions")

        self.add_file_menu_actions(action_group)

        uimanager = self.create_ui_manager()
        uimanager.insert_action_group(action_group)

        menubar = uimanager.get_widget("/MenuBar")

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        box.pack_start(menubar, False, False, 0)

        toolbar = uimanager.get_widget("/ToolBar")
        box.pack_start(toolbar, False, False, 0)


        self.vp = Gtk.HPaned()
        box.pack_start(self.vp, True, True, 0)

        # the data are stored in the model
        # create a treestore with two columns
        self.store = Gtk.TreeStore(str, str, str)
        
        # the treeview shows the model
        # create a treeview on the model self.store
        view = Gtk.TreeView()
        view.set_model(self.store)

        # the cellrenderer for the first column - text
        renderer_books = Gtk.CellRendererText()
        # the first column is created
        main_column = Gtk.TreeViewColumn(None, renderer_books, text=2)
        # and it is appended to the treeview
        view.append_column(main_column)

        self.selection = view.get_selection()
        self.selection.connect("changed", self.on_tree_selection_changed)

        scrolled_window_left = Gtk.ScrolledWindow()
        scrolled_window_left.set_border_width(5)
        scrolled_window_left.set_policy(
            Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scrolled_window_left.add(view)
        self.vp.add1(scrolled_window_left)

        self.scrolled_window = Gtk.ScrolledWindow()
        self.scrolled_window.set_border_width(5)
        # we scroll only if needed
        self.scrolled_window.set_policy(
            Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        self.vp.add2(self.scrolled_window)

        self.add(box)

    def on_tree_selection_changed(self, selection):
        model, treeiter = self.selection.get_selected()
        if treeiter is None:
            return
        elif model[treeiter][0] == "root":
            return self.show_choreography_source()
        elif model[treeiter][0] == "choreography-graph":
            return self.show_choreography_graph()

        key = (model[treeiter][0], model[treeiter][1])
        if not key in self.tree_mapping:
            return
        val = self.tree_mapping[key]
        if key[0] == "semantics-pom":
            self.show_pomset_graph(val)
        elif key[0] == "cc2-closure-pom":
            self.show_cc2_closure(val)
        elif key[0] == "cc2-counterexamples-pom":
            self.show_cc2_closure(val)
        elif key[0] == "cc2-counterexamples-sgg":
            self.show_cc2_sgg(val)
        elif key[0] == "cc2-counterexamples-diff":
            self.show_cc2_diff(val)
        elif key[0] == "cc3-closure-pom":
            self.show_cc3_closure(val)
        elif key[0] == "cc3-counterexamples-pom":
            self.show_cc3_closure(val)
        elif key[0] == "cc3-counterexamples-sgg":
            self.show_cc3_sgg(val)
        elif key[0] == "cc3-counterexamples-diff":
            self.show_cc3_diff(val)

    def add_file_menu_actions(self, action_group):
        action_filemenu = Gtk.Action("FileMenu", "File", None, None)
        action_group.add_action(action_filemenu)

        action_filenewmenu = Gtk.Action("FileNew", None, None, Gtk.STOCK_NEW)
        action_group.add_action(action_filenewmenu)

        action_new = Gtk.Action("FileNewStandard", "_New",
            "Create a new file", Gtk.STOCK_NEW)
        action_new.connect("activate", self.on_menu_file_new_generic)
        action_group.add_action_with_accel(action_new, None)

        action_group.add_actions([
            ("FileNewFoo", None, "New Foo", None, "Create new foo",
             self.on_menu_file_new_generic),
            ("FileNewGoo", None, "_New Goo", None, "Create new goo",
             self.on_menu_file_new_generic),
        ])

        action_filequit = Gtk.Action("FileQuit", None, None, Gtk.STOCK_QUIT)
        action_filequit.connect("activate", self.on_menu_file_quit)
        action_group.add_action(action_filequit)

        action_fileopen = Gtk.Action("FileOpenChoreography", "_Open", "Open .sgg", Gtk.STOCK_OPEN)
        action_fileopen.connect("activate", self.on_menu_file_open)
        action_group.add_action_with_accel(action_fileopen)

        action_semantics = Gtk.Action("FileGenSemantics", "Generate _Semantics", "Generate Pomset Semantics", None)
        action_semantics.connect("activate", self.on_menu_gen_semantics)
        action_group.add_action_with_accel(action_semantics, "<Control>s")

        action_cc2 = Gtk.Action("CC2", "CC_2", "Closure Condition 2", None)
        action_cc2.connect("activate", self.on_menu_cc2)
        action_group.add_action_with_accel(action_cc2, "<Control>2")

        action_cc3 = Gtk.Action("CC3", "CC_3", "Closure Condition 3", None)
        action_cc3.connect("activate", self.on_menu_cc3)
        action_group.add_action_with_accel(action_cc3, "<Control>3")
        
        action_pom2sgg = Gtk.Action("pom2sgg", "Generate Choreography", "Generate Choreography", None)
        action_pom2sgg.connect("activate", self.on_menu_pom2sgg)
        action_group.add_action_with_accel(action_pom2sgg, "<Control>p")

        action_sgg2diff = Gtk.Action("sgg2diff", "Compare", "Compare Choreography", None)
        action_sgg2diff.connect("activate", self.on_menu_sgg2diff)
        action_group.add_action_with_accel(action_sgg2diff, "<Control>d")
        
    def create_ui_manager(self):
        uimanager = Gtk.UIManager()

        # Throws exception if something went wrong
        uimanager.add_ui_from_string(UI_INFO)

        # Add the accelerator group to the toplevel window
        accelgroup = uimanager.get_accel_group()
        self.add_accel_group(accelgroup)
        return uimanager

    def on_menu_file_new_generic(self, widget):
        print("A File|New menu item was selected.")

    def on_menu_file_open(self, widget):
        dialog = Gtk.FileChooserDialog("Please choose a choreography", self,
            Gtk.FileChooserAction.OPEN,
            (Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL,
             Gtk.STOCK_OPEN, Gtk.ResponseType.OK))
        self.add_filters(dialog)
        response = dialog.run()
        
        if response == Gtk.ResponseType.OK:
            self.workspace = Workspace(dialog.get_filename())
            dialog.destroy()
        elif response == Gtk.ResponseType.CANCEL:
            dialog.destroy()
            return

        self.store.clear()
        self.workspace.gen_choreography_png()
        
        choreography = self.store.append(
            None,
            ["root", None, self.workspace.get_root_folder()])
        choreography_png = self.store.append(
            choreography,
            ["choreography-graph", None, "graph"])
        self.tree_mapping = {}

        self.show_choreography_source()

    def remove_tree_root_section(self, section):
        it = self.store.get_iter_first()
        while (not it is None):
            if self.store[it][0] == section:
                self.store.remove(it)
                break
            it = self.store.iter_next(it)
        

    def on_menu_gen_semantics(self, widget):
        self.workspace.gen_semantics()
        self.remove_tree_root_section("semantics")
        semantics = self.store.append(None, ["semantics", None, "semantics"])
        i = 0
        for f in self.workspace.semantics:
            self.store.append(semantics, ["semantics-pom", str(i), "pomset %d"%i])
            self.tree_mapping[("semantics-pom", str(i))] = f
            i+=1

    def closure_res_to_tree(self, closure, res):
        self.remove_tree_root_section("cc%d"%closure)
        cc_list = self.store.append(None, ["cc%d"%closure, None, "CC %d"%closure])
        closure_list = self.store.append(cc_list, ["cc%d-closure"%closure, None, "closure"])
        counterexamples_list = self.store.append(cc_list, ["cc%d-counterexamples"%closure, None, "counterexamples"])

        for pm in res["closure"]:
            str_view = "pomset %d"%pm
            if pm in res["mapping"]:
                str_view += " -> %d" % res["mapping"][pm]
            self.store.append(closure_list, ["cc%d-closure-pom"%closure, str(pm), str_view])
            self.tree_mapping[("cc%d-closure-pom"%closure, str(pm))] = pm
            if not pm in res["mapping"]:
                self.store.append(counterexamples_list, ["cc%d-counterexamples-pom"%closure, str(pm), str_view])
                self.tree_mapping[("cc%d-counterexamples-pom"%closure, str(pm))] = pm
        
    def on_menu_cc2(self, widget):
        self.workspace.gen_cc2()
        self.closure_res_to_tree(2, self.workspace.cc2)

    def get_selected_cc_pom_idx(self, closure):
        model, treeiter = self.selection.get_selected()
        if treeiter is None:
            return None
        key = (model[treeiter][0], model[treeiter][1])
        if key[0] == ("cc%d-counterexamples-pom"%closure):
            return
        if not key in self.tree_mapping:
            return
        
    def on_menu_pom2sgg(self, widget):
        model, treeiter = self.selection.get_selected()
        if treeiter is None:
            return
        key = (model[treeiter][0], model[treeiter][1])
        if key[0] != "cc2-counterexamples-pom":
            return
        if not key in self.tree_mapping:
            return

        pom = self.tree_mapping[key]
        self.workspace.gen_cc2_choreography(
            pom
        )

        self.store.append(treeiter, ["cc2-counterexamples-sgg", str(pom), "graph"])
        self.tree_mapping[("cc2-counterexamples-sgg", str(pom))] = pom
                
    def on_menu_sgg2diff(self, widget):
        model, treeiter = self.selection.get_selected()
        if treeiter is None:
            return
        key = (model[treeiter][0], model[treeiter][1])
        if key[0] != "cc2-counterexamples-sgg":
            return
        if not key in self.tree_mapping:
            return
        pom = self.tree_mapping[key]

        diffs = self.workspace.gen_cc2_diff(
            pom
        )

        diff_iter = self.store.append(treeiter, ["cc2-counterexamples-diff-list", None, "diffs"])
        for i in diffs:
            new_iter = self.store.append(diff_iter, ["cc2-counterexamples-diff", "%d-%d"%(pom, i), "%d: %f"%(i, diffs[i])])
            self.tree_mapping[("cc2-counterexamples-diff", "%d-%d"%(pom, i))] = (pom, i)
            
    def on_menu_cc3(self, widget):
        self.workspace.gen_cc3()
        self.closure_res_to_tree(3, self.workspace.cc3)

    def on_menu_pom3sgg(self, widget):
        return
    def on_menu_sgg3diff(self, widget):
        return

    def change_main_view(self, widget):
        old_views = self.scrolled_window.get_children()
        for old in old_views:
            self.scrolled_window.remove(old)
        self.scrolled_window.add(widget)
        self.scrolled_window.show_all()
        
    def show_choreography_source(self):
        self.change_main_view(
            Gtk.Label(open(self.workspace.sgg_absolute_path).read())
        )
        
    def show_choreography_graph(self):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_choreography_png_path()
            ))


    def show_pomset_graph(self, f):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_semantics_png_path(f)
            ))

    def show_cc2_closure(self, i):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc2_closure_png_path(i)
            ))

    def show_cc2_sgg(self, i):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc2_counter_choreography_png(i)
            ))

    def show_cc2_diff(self, val):
        (pom_id, i) = val
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc2_diff_path(pom_id, i)
            ))

    def show_cc3_closure(self, i):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc3_closure_png_path(i)
            ))

    def show_cc3_sgg(self, i):
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc3_counter_choreography_png(i)
            ))

    def show_cc3_diff(self, val):
        (pom_id, i) = val
        self.change_main_view(
            Gtk.Image.new_from_file(
                self.workspace.get_cc3_diff_path(pom_id, i)
            ))

    def add_filters(self, dialog):
        filter_sgg = Gtk.FileFilter()
        filter_sgg.set_name("sgg files")
        filter_sgg.add_pattern("*.sgg")
        dialog.add_filter(filter_sgg)

        filter_any = Gtk.FileFilter()
        filter_any.set_name("Any files")
        filter_any.add_pattern("*")
        dialog.add_filter(filter_any)


    def on_menu_file_quit(self, widget):
        Gtk.main_quit()



win = MainWindow()
win.connect("destroy", Gtk.main_quit)
win.show_all()
Gtk.main()