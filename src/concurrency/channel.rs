extern crate rustc_data_structures;
extern crate rustc_middle;

use petgraph::graph::NodeIndex;
use petgraph::visit::{IntoNodeReferences, NodeRef};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::{self, EarlyBinder, Instance, TyCtxt, TyKind, TypingEnv};
use rustc_span::Span;

use crate::memory::pointsto::AliasId;
use crate::translate::callgraph::{CallGraph, CallGraphNode, InstanceId};

use serde_json::json;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChannelType {
    Mpsc,
    Sync(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EndpointType {
    Sender,
    Receiver,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChannelId {
    pub instance_id: InstanceId,
    pub local: Local,
}

impl<'tcx> ChannelId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self { instance_id, local }
    }

    pub fn get_alias_id(&self) -> AliasId {
        AliasId::new(self.instance_id, self.local)
    }
}

#[derive(Debug)]
pub enum ChannelResult<'tcx> {
    Single(ChannelType, EndpointType, ty::Ty<'tcx>),

    Pair(
        (ChannelType, EndpointType, ty::Ty<'tcx>),
        (ChannelType, EndpointType, ty::Ty<'tcx>),
    ),
}

#[derive(Debug, Clone)]
pub struct ChannelInfo<'tcx> {
    pub instance: DefId,
    pub channel_type: ChannelType,
    pub endpoint_type: EndpointType,
    pub data_type: ty::Ty<'tcx>,
    pub span: Span,
}

impl<'tcx> ChannelInfo<'tcx> {
    pub fn new(
        instance: DefId,
        channel_type: ChannelType,
        endpoint_type: EndpointType,
        data_type: ty::Ty<'tcx>,
        span: Span,
    ) -> Self {
        Self {
            instance,
            channel_type,
            endpoint_type,
            data_type,
            span,
        }
    }
}

pub type ChannelMap<'tcx> = FxHashMap<ChannelId, ChannelInfo<'tcx>>;
pub type ChannelTuple<'tcx> = FxHashMap<ChannelId, (ChannelInfo<'tcx>, ChannelInfo<'tcx>)>;

pub struct ChannelCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    crate_name: String,
    pub channels: ChannelMap<'tcx>,
    pub channel_tuples: ChannelTuple<'tcx>,
}

impl<'a, 'tcx> ChannelCollector<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, crate_name: String) -> Self {
        Self {
            tcx,
            callgraph,
            crate_name,
            channels: Default::default(),
            channel_tuples: Default::default(),
        }
    }

    pub fn analyze(&mut self) {
        for node_ref in self.callgraph.graph.node_references() {
            if let CallGraphNode::WithBody(instance) = node_ref.weight() {
                let body = self.tcx.instance_mir(instance.def);
                self.analyze_function(node_ref.0, *instance, body);
            }
        }
    }

    pub fn analyze_function(
        &mut self,
        instance_id: NodeIndex,
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
    ) {
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let typing_env = TypingEnv::post_analysis(self.tcx, instance.def_id());
            let local_ty = instance.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                EarlyBinder::bind(local_decl.ty),
            );

            if let Some(channel_result) = self.get_channel_info(local_ty) {
                match channel_result {
                    ChannelResult::Single(channel_type, endpoint_type, data_type) => {
                        let channel_id = ChannelId::new(instance_id, local);
                        let channel_info = ChannelInfo::new(
                            instance.def_id(),
                            channel_type,
                            endpoint_type,
                            data_type,
                            local_decl.source_info.span,
                        );
                        self.channels.insert(channel_id, channel_info);
                    }
                    ChannelResult::Pair(sender_info, receiver_info) => {
                        let channle_id = ChannelId::new(instance_id, local);
                        let sender_channel_info = ChannelInfo::new(
                            instance.def_id(),
                            sender_info.0,
                            sender_info.1,
                            sender_info.2,
                            local_decl.source_info.span,
                        );

                        let receiver_channel_info = ChannelInfo::new(
                            instance.def_id(),
                            receiver_info.0,
                            receiver_info.1,
                            receiver_info.2,
                            local_decl.source_info.span,
                        );

                        self.channel_tuples
                            .insert(channle_id, (sender_channel_info, receiver_channel_info));
                    }
                }
            }
        }
    }

    fn get_channel_info(&self, ty: ty::Ty<'tcx>) -> Option<ChannelResult<'tcx>> {
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                let path = self.tcx.def_path_str(adt_def.did());
                let data_type = substs.types().next()?;

                if path.starts_with("std::sync::mpsc::Sender") {
                    Some(ChannelResult::Single(
                        ChannelType::Mpsc,
                        EndpointType::Sender,
                        data_type,
                    ))
                } else if path.starts_with("std::sync::mpsc::Receiver") {
                    Some(ChannelResult::Single(
                        ChannelType::Mpsc,
                        EndpointType::Receiver,
                        data_type,
                    ))
                } else if path.starts_with("std::sync::mpsc::SyncSender") {
                    Some(ChannelResult::Single(
                        ChannelType::Sync(0),
                        EndpointType::Sender,
                        data_type,
                    ))
                } else {
                    None
                }
            }

            TyKind::Tuple(types) => {
                if types.len() == 2 {
                    let sender_ty = types[0];
                    let receiver_ty = types[1];

                    if let (TyKind::Adt(sender_def, sender_substs), TyKind::Adt(receiver_def, _)) =
                        (sender_ty.kind(), receiver_ty.kind())
                    {
                        let sender_path = self.tcx.def_path_str(sender_def.did());
                        let receiver_path = self.tcx.def_path_str(receiver_def.did());

                        if sender_path.starts_with("std::sync::mpsc::Sender")
                            && receiver_path.starts_with("std::sync::mpsc::Receiver")
                        {
                            let data_type = sender_substs.types().next()?;
                            Some(ChannelResult::Pair(
                                (ChannelType::Mpsc, EndpointType::Sender, data_type),
                                (ChannelType::Mpsc, EndpointType::Receiver, data_type),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    #[allow(dead_code)]
    pub fn to_json_pretty(&self) -> Result<(), serde_json::Error> {
        if self.channels.is_empty() {
            log::debug!("No channels found");
        } else {
            for (channel_id, info) in self.channels.iter() {
                let channel_info = json!({
                    "location": {
                        "instance": self.tcx.def_path_str(info.instance),
                        "local": channel_id.local.index(),
                    },
                    "channel_type": match info.channel_type {
                        ChannelType::Mpsc => "Mpsc".to_string(),
                        ChannelType::Sync(capacity) => {
                            format!("Sync({})", capacity)
                        }
                    },
                    "endpoint_type": format!("{:?}", info.endpoint_type),
                    "data_type": info.data_type.to_string(),
                    "defined_at": format!("{:?}", info.span),
                });

                log::info!(
                    "Channel Info:\n{}",
                    serde_json::to_string_pretty(&channel_info).unwrap()
                );
            }
        }
        if self.channel_tuples.is_empty() {
            log::debug!("No channel tuples found");
        } else {
            for (channel_id, (sender_info, receiver_info)) in self.channel_tuples.iter() {
                let channel_sender = json!({
                    "location": {
                        "instance": self.tcx.def_path_str(sender_info.instance),
                        "local": channel_id.local.index(),
                    },
                    "channel_type": match sender_info.channel_type {
                        ChannelType::Mpsc => "Mpsc".to_string(),
                        ChannelType::Sync(capacity) => {
                            format!("Sync({})", capacity)
                        }
                    },
                    "endpoint_type": format!("{:?}", sender_info.endpoint_type),
                    "data_type": sender_info.data_type.to_string(),
                    "defined_at": format!("{:?}", sender_info.span),
                });
                let channel_receiver = json!({
                    "location": {
                        "instance": self.tcx.def_path_str(receiver_info.instance),
                        "local": channel_id.local.index(),
                    },
                    "channel_type": match receiver_info.channel_type {
                        ChannelType::Mpsc => "Mpsc".to_string(),
                        ChannelType::Sync(capacity) => {
                            format!("Sync({})", capacity)
                        }
                    },
                    "endpoint_type": format!("{:?}", receiver_info.endpoint_type),
                    "data_type": receiver_info.data_type.to_string(),
                    "defined_at": format!("{:?}", receiver_info.span),
                });
                log::info!(
                    "Channel Tuple Info:\n{} and {}",
                    serde_json::to_string_pretty(&channel_sender).unwrap(),
                    serde_json::to_string_pretty(&channel_receiver).unwrap()
                );
            }
        }
        Ok(())
    }

    pub fn print_debug_info(&self) {
        if self.channels.is_empty() && self.channel_tuples.is_empty() {
            log::debug!("No channels found in crate: {}", self.crate_name);
            return;
        }

        log::debug!("Channel analysis results for crate: {}", self.crate_name);

        if !self.channels.is_empty() {
            log::debug!("Individual channels:");
            for (channel_id, info) in self.channels.iter() {
                log::debug!("  Function: {}", self.tcx.def_path_str(info.instance));
                log::debug!("    Local: {:?}", channel_id.local);
                log::debug!("    Type: {:?}", info.channel_type);
                log::debug!("    Endpoint: {:?}", info.endpoint_type);
                log::debug!("    Data Type: {}", info.data_type);
                log::debug!("    Defined at: {:?}", info.span);
                log::debug!("----------------------------------------");
            }
        }

        if !self.channel_tuples.is_empty() {
            log::debug!("Channel pairs:");
            for (sender_id, (sender_info, receiver_info)) in self.channel_tuples.iter() {
                log::debug!(
                    "  Function: {}",
                    self.tcx.def_path_str(sender_info.instance)
                );
                log::debug!("    Sender:");
                log::debug!("      Local: {:?}", sender_id.local);
                log::debug!("      Type: {:?}", sender_info.channel_type);
                log::debug!("      Data Type: {}", sender_info.data_type);
                log::debug!("    Receiver:");
                log::debug!("      Type: {:?}", receiver_info.channel_type);
                log::debug!("      Data Type: {}", receiver_info.data_type);
                log::debug!("    Defined at: {:?}", sender_info.span);
                log::debug!("----------------------------------------");
            }
        }
    }
}
