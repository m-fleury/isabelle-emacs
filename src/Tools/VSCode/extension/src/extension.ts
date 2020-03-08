'use strict';

import * as path from 'path';
import * as fs from 'fs';
import { setInterval, clearInterval } from 'timers';
import * as library from './library'
import * as decorations from './decorations';
import * as preview_panel from './preview_panel';
import * as protocol from './protocol';
import * as state_panel from './state_panel';
import * as symbol from './symbol';
import * as completion from './completion';
import { Uri, TextEditor, ViewColumn, Selection, Position, ExtensionContext, workspace, window,
  commands, languages } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind,
  NotificationType } from 'vscode-languageclient';


let last_caret_update: protocol.Caret_Update = {}

export function activate(context: ExtensionContext)
{
  const isabelle_home = library.get_configuration<string>("home")
  const isabelle_args = library.get_configuration<Array<string>>("args")
  const cygwin_root = library.get_configuration<string>("cygwin_root")
  const debug = library.get_configuration<boolean>("debug")
  let progress_timer: NodeJS.Timer
  let progress_update_interval : number = library.get_configuration<number>("progress-update-interval") || 1500

  /* server */

  if (isabelle_home === "")
    window.showErrorMessage("Missing user settings: isabelle.home")
  else {
    const isabelle_tool = isabelle_home + "/bin/isabelle
    const standard_args = ["-o", "vscode_unicode_symbols", "-o", "vscode_pide_extensions"]

    const server_options: ServerOptions =
      library.platform_is_windows() ?
        { command:
            (cygwin_root === "" ? path.join(isabelle_home, "contrib", "cygwin") : cygwin_root) +
            "/bin/bash",
          args: ["-l", isabelle_tool, "vscode_server"].concat(standard_args, isabelle_args) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(standard_args, isabelle_args) };
    const language_client_options: LanguageClientOptions = {
      documentSelector: [
        { language: "isabelle", scheme: "file" },
        { language: "isabelle-ml", scheme: "file" },
        { language: "bibtex", scheme: "file" }
      ]
    };
    if (debug)
      console.log("creating language_client now")
    var language_client;
    try {
      language_client =
        new LanguageClient("Isabelle", server_options, language_client_options, debug)
      language_client.onReady();
    }
    catch(e)  {
      console.error("could not start Isabelle " + e)
    }
    if (debug)
      console.log("created language_client");

    if (debug)
      language_client.onReady().then(() =>  console.log("language_client fully loaded"))

    /* decorations */

    decorations.setup(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => decorations.setup(context)),
      workspace.onDidChangeTextDocument(event => decorations.touch_document(event.document)),
      window.onDidChangeActiveTextEditor(decorations.update_editor),
      workspace.onDidCloseTextDocument(decorations.close_document))

    language_client.onReady().then(() =>
      language_client.onNotification(protocol.decoration_type, decorations.apply_decoration))


    /* caret handling */

    function update_caret()
    {
      const editor = window.activeTextEditor
      let caret_update: protocol.Caret_Update = {}
      if (editor) {
        const uri = editor.document.uri
        const cursor = editor.selection.active
        if (library.is_file(uri) && cursor)
          caret_update = { uri: uri.toString(), line: cursor.line, character: cursor.character }
      }
      if (last_caret_update !== caret_update) {
        if (caret_update.uri)
          language_client.sendNotification(protocol.caret_update_type, caret_update)
        //console.log("last caret was: " + last_caret_update)
        //console.log("new caret was: " + caret_update)

        last_caret_update = caret_update
      }
    }

    function goto_file(caret_update: protocol.Caret_Update)
    {
      function move_cursor(editor: TextEditor)
      {
        const pos = new Position(caret_update.line || 0, caret_update.character || 0)
        editor.selections = [new Selection(pos, pos)]
      }

      if (caret_update.uri) {
        workspace.openTextDocument(Uri.parse(caret_update.uri)).then(document =>
        {
          const editor = library.find_file_editor(document.uri)
          const column = editor ? editor.viewColumn : ViewColumn.One
          window.showTextDocument(document, column, !caret_update.focus).then(move_cursor)
        })
      }
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(_ => update_caret()),
        window.onDidChangeTextEditorSelection(_ => update_caret()))
      update_caret()

      language_client.onNotification(protocol.caret_update_type, goto_file)
    })


    /* dynamic output */

    const dynamic_output = window.createOutputChannel("Isabelle Output")
    context.subscriptions.push(dynamic_output)
    dynamic_output.show(true)
    dynamic_output.hide()

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.dynamic_output_type,
        params => { dynamic_output.clear(); dynamic_output.appendLine(params.content) })
    })


    /* state panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.state", uri => state_panel.init(uri)))

    language_client.onReady().then(() => state_panel.setup(context, language_client))


    /* preview panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => preview_panel.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => preview_panel.request(uri, true)))

    language_client.onReady().then(() => preview_panel.setup(context, language_client))


    /* Isabelle symbols */

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.symbols_type,
        params => symbol.setup(context, params.entries))
      language_client.sendNotification(protocol.symbols_request_type)
    })


    /* completion */

    const completion_provider = new completion.Completion_Provider
    for (const mode of ["isabelle", "isabelle-ml"]) {
      context.subscriptions.push(
        languages.registerCompletionItemProvider({scheme: 'file', language: mode}, completion_provider))
    }


    /* spell checker */

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        commands.registerCommand("isabelle.include-word", uri =>
          language_client.sendNotification(protocol.include_word_type)),
        commands.registerCommand("isabelle.include-word-permanently", uri =>
          language_client.sendNotification(protocol.include_word_permanently_type)),
        commands.registerCommand("isabelle.exclude-word", uri =>
          language_client.sendNotification(protocol.exclude_word_type)),
        commands.registerCommand("isabelle.exclude-word-permanently", uri =>
          language_client.sendNotification(protocol.exclude_word_permanently_type)),
        commands.registerCommand("isabelle.reset-words", uri =>
          language_client.sendNotification(protocol.reset_words_type)))
    })


    /* progress */
    const theories_output = window.createOutputChannel("Isabelle Theories")
    context.subscriptions.push(theories_output)
    theories_output.show(true)
    theories_output.hide()

    function node_status_print(st: [protocol.Node_Status]) : string {
      var res =
      st.forEach(st => {
          let processed_tasks : number = st.finished + st.warned
	  let unfinished_tasks : number = st.unprocessed + st.running + st.failed
          let total_tasks : number = processed_tasks + unfinished_tasks
          var progress : number
          if (st.initialized && total_tasks != 0) {
            progress = 100.0 * processed_tasks / total_tasks
          }
          else progress = 0

          if(st.failed != 0 && st.canceled !=0)
	                           res += "✘
          else if(st.running != 0) res += "☛☛
          else if(unfinished_tasks == 0 && st.consolidated && st.finished)
                                   res += "☑✔
          else if(st.finished)     res += " ✔
          else                     res +=

	  let theory_name = st.name.split("/").pop()
          res += theory_name + " (progress: " + progress.toFixed(0) + "% , " + "warnings: " + st.warned + ")\n
      })
      return res
    }

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.progress_response_type,
				     (params : protocol.Nodes_Status) => {
          let new_status = node_status_print(params.nodes_status)
          theories_output.clear();
					theories_output.appendLine(new_status) })
    })

    function progress_update() {
      language_client.onReady().then(() =>
        language_client.sendNotification(protocol.progress_request_type))
    }
    function stop_progress_update() {
      if(progress_timer)
        clearInterval(progress_timer)
      progress_timer = undefined
      theories_output.clear()
      theories_output.appendLine("Printing suspended, use isabelle.start-progress-update to restart")
    }

    function start_progress_update() {
      clearInterval(progress_timer)
      progress_timer = setInterval(progress_update, progress_update_interval)
      theories_output.clear()
      theories_output.appendLine("Printing activated, awaiting answer from Isabelle")

    }

    function change_progress_update(int) {
      stop_progress_update()
      progress_update_interval = int
      progress_timer = setInterval(progress_update, progress_update_interval)
      if(progress_timer)
        start_progress_update()
    }


    context.subscriptions.push(
      commands.registerCommand("isabelle.set-progress-interval (ms)", change_progress_update),
      commands.registerCommand("isabelle.stop-progress-update", stop_progress_update),
      commands.registerCommand("isabelle.start-progress-update", start_progress_update))


    /* start server */

    context.subscriptions.push(language_client.start())

    // only start timer when the server is ready
    progress_timer = setInterval(progress_update, progress_update_interval)

  }

}

export function deactivate() { }
