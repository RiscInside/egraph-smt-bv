use std::{fs::File, io::Write, path::PathBuf};

use anyhow::Context as _;
use egglog::{
    ast::{Command, GenericSchedule, RunConfig},
    span, SerializeConfig,
};
use indoc::formatdoc;
use itertools::Itertools as _;

use crate::Context;

fn json_string_for(graph: &egraph_serialize::EGraph) -> String {
    let mut json_string = Vec::<u8>::new();
    serde_json::to_writer_pretty(&mut json_string, &graph).unwrap();
    format!("{:?}", String::from_utf8(json_string).unwrap())
}

fn dump_html_for_graphs(path: &PathBuf, graphs: &[egraph_serialize::EGraph]) -> anyhow::Result<()> {
    let strings = graphs.iter().map(json_string_for).join(",\n");

    let html = formatdoc!(
        r#"
        <div id="egraph-visualizer"></div>
        <link rel="stylesheet" href="https://esm.sh/egraph-visualizer/dist/style.css" />
        <script type="module">
            import {{ mount }} from "https://esm.sh/egraph-visualizer";
            const mounted = mount(document.getElementById("egraph-visualizer"));
            mounted.render([{strings}]);
            // later can call mounted.unmount() to remove the visualizer
        </script>"#
    );
    File::create(path)?.write_all(html.as_bytes())?;
    Ok(())
}

impl Context {
    pub(crate) fn serialize(&mut self) -> anyhow::Result<egraph_serialize::EGraph> {
        // Clean the e-graph
        self.egraph.push();
        self.egraph
            .run_program(vec![Command::RunSchedule(GenericSchedule::Run(
                span!(),
                RunConfig {
                    ruleset: "vis".into(),
                    until: None,
                },
            ))])?;

        let mut serialized = self.egraph.serialize(SerializeConfig::default());
        serialized.split_classes(|_, node| node.op == "true" || node.op == "false");
        serialized.saturate_inline_leaves();
        self.egraph.pop().unwrap();

        Ok(serialized)
    }

    pub fn dump_json(&mut self, path: &PathBuf) -> anyhow::Result<()> {
        self.serialize()?
            .to_json_file(path)
            .context("dumping json for the e-graph")?;
        Ok(())
    }

    pub fn dump_html(&mut self, path: &PathBuf) -> anyhow::Result<()> {
        let serialized = self.serialize()?;
        dump_html_for_graphs(path, &[serialized])
    }

    pub fn dump_html_history(&mut self, path: &PathBuf) -> anyhow::Result<()> {
        if let Some(history) = &self.rewriting_history {
            dump_html_for_graphs(path, history)
        } else {
            Ok(())
        }
    }
}
