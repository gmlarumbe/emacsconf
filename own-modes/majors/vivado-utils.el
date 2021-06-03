;;; vivado-utils.el --- Vivado Utils  -*- lexical-binding: t -*-
;;; Commentary:
;; This package includes one minor mode to add auto completion to a Vivado TCL comint shell,
;; and a major mode to edit Vivado XDC files (tcl mode derived)
;;
;; TCL shell depends on compilation-settings.el `larumbe/shell-compilation-regexp-interactive' function,
;; and on the compilation regexps association lists defined there.
;;
;; Therefore, in the future it could be packaged as a single file, with proper (require) dependencies.
;;
;;; Code:


;;; Vivado-TCL Shell
(defvar larumbe/vivado-tcl-shell-buffer "*vivado-tcl*")
(defvar larumbe/vivado-tcl-commands '(
       ;; UG835 Xilinx words converted to text via `pdftotext'

       ;; Board:
       "apply_board_connection"      "current_board"                 "current_board_part"
       "get_board_bus_nets"          "get_board_buses"               "get_board_component_interfaces"
       "get_board_component_modes"   "get_board_component_pins"      "get_board_components"
       "get_board_interface_ports"   "get_board_ip_preferences"      "get_board_jumpers"
       "get_board_parameters"        "get_board_part_interfaces"     "get_board_part_pins"
       "get_board_parts"             "get_boards"

       ;; Configuration:
       "config_implementation"

       ;; CreatePeripheral:
       "add_peripheral_interface"    "create_peripheral"              "generate_peripheral"
       "write_peripheral"

       ;; Debug:
       "apply_hw_ila_trigger"        "connect_debug_cores"            "connect_debug_port"
       "create_debug_core"           "create_debug_port"              "delete_debug_core"
       "delete_debug_port"           "disconnect_debug_port"          "get_debug_cores"
       "get_debug_ports"             "implement_debug_core"           "modify_debug_ports"
       "report_debug_core"           "write_debug_probes"

       ;; DRC:
       "add_drc_checks"              "create_drc_check"               "create_drc_ruledeck"
       "create_drc_violation"        "create_waiver"                  "delete_drc_check"
       "delete_drc_ruledeck"         "get_drc_checks"                 "get_drc_ruledecks"
       "get_drc_violations"          "remove_drc_checks"              "report_drc"
       "reset_drc"                   "reset_drc_check"

       ;; Feasibility:
       "delete_qor_suggestions"      "get_qor_suggestions"            "read_qor_suggestions"
       "report_qor_assessment"       "report_qor_suggestions"         "write_qor_suggestions"

       ;; FileIO:
       "auto_detect_xpm"             "config_webtalk"                 "create_port_on_reconfigurable_module"
       "decrypt_bitstream"           "encrypt"                        "generate_base_platform"
       "generate_mem_files"          "generate_pblock"                "generate_rl_platform"
       "generate_shx_platform"       "infer_diff_pairs"               "open_hw_platform"
       "pr_recombine"                "pr_subdivide"                   "pr_verify"
       "read_bd"                     "read_checkpoint"                "read_csv"
       "read_edif"                   "read_ip"                        "read_mem"
       "read_qor_suggestions"        "read_saif"                      "read_schematic"
       "read_twx"                    "read_verilog"                   "read_vhdl"
       "read_xdc"                    "refresh_meminit"                "write_abstract_shell"
       "write_bd_layout"             "write_bitstream"                "write_bmm"
       "write_bsdl"                  "write_cfgmem"                   "write_checkpoint"
       "write_csv"                   "write_debug_probes"             "write_edif"
       "write_hw_platform"           "write_hw_platform_metadata"     "write_ibis"
       "write_inferred_xdc"          "write_mem_info"                 "write_qor_suggestions"
       "write_schematic"             "write_sdf"                      "write_verilog"
       "write_vhdl"                  "write_xdc"

       ;; Floorplan:
       "add_cells_to_pblock"           "create_pblock"                     "delete_pblocks"
       "delete_rpm"                    "get_pblocks"                       "place_cell"
       "place_pblocks"                 "remove_cells_from_pblock"          "resize_pblock"
       "swap_locs"                     "unplace_cell"

       ;; GUIControl:
       "create_gui_custom_command"     "create_gui_custom_command_arg"     "endgroup"
       "get_gui_custom_command_args"   "get_gui_custom_commands"           "get_highlighted_objects"
       "get_marked_objects"            "get_selected_objects"              "highlight_objects"
       "mark_objects"                  "redo"                              "remove_gui_custom_command_args"
       "remove_gui_custom_commands"    "select_objects"                    "show_objects"
       "show_schematic"                "start_gui"                         "startgroup"
       "stop_gui"                      "undo"                              "unhighlight_objects"
       "unmark_objects"                "unselect_objects"

       ;; Hardware:
       "add_hw_hbm_pc"                 "add_hw_probe_enum"                 "boot_hw_device"
       "close_hw_manager"              "close_hw_target"                   "commit_hw_hbm"
       "commit_hw_mig"                 "commit_hw_sio"                     "commit_hw_sysmon"
       "commit_hw_vio"                 "config_hw_sio_gts"                 "connect_hw_server"
       "create_hw_axi_txn"             "create_hw_bitstream"               "create_hw_cfgmem"
       "create_hw_device"              "create_hw_probe"                   "create_hw_sio_link"
       "create_hw_sio_linkgroup"       "create_hw_sio_scan"                "create_hw_sio_sweep"
       "create_hw_target"              "current_hw_cfgmem"                 "current_hw_device"
       "current_hw_ila"                "current_hw_ila_data"               "current_hw_server"
       "current_hw_target"             "delete_hw_axi_txn"                 "delete_hw_bitstream"
       "delete_hw_cfgmem"              "delete_hw_probe"                   "delete_hw_target"
       "detect_hw_sio_links"           "disconnect_hw_server"              "display_hw_ila_data"
       "display_hw_sio_scan"           "execute_hw_svf"                    "get_cfgmem_parts"
       "get_hw_axi_txns"               "get_hw_axis"                       "get_hw_cfgmems"
       "get_hw_ddrmcs"                 "get_hw_devices"                    "get_hw_hbms"
       "get_hw_ila_datas"              "get_hw_ilas"                       "get_hw_migs"
       "get_hw_probes"                 "get_hw_servers"                    "get_hw_sio_commons"
       "get_hw_sio_gtgroups"           "get_hw_sio_gts"                    "get_hw_sio_iberts"
       "get_hw_sio_linkgroups"         "get_hw_sio_links"                  "get_hw_sio_plls"
       "get_hw_sio_rxs"                "get_hw_sio_scans"                  "get_hw_sio_sweeps"
       "get_hw_sio_txs"                "get_hw_sysmon_reg"                 "get_hw_sysmons"
       "get_hw_targets"                "get_hw_vios"                       "list_hw_samples"
       "open_hw_manager"               "open_hw_target"                    "pause_hw_hbm_amon"
       "program_hw_cfgmem"             "program_hw_devices"                "read_hw_ila_data"
       "read_hw_sio_scan"              "read_hw_sio_sweep"                 "readback_hw_cfgmem"
       "readback_hw_device"            "refresh_hw_axi"                    "refresh_hw_ddrmc"
       "refresh_hw_device"             "refresh_hw_hbm"                    "refresh_hw_mig"
       "refresh_hw_server"             "refresh_hw_sio"                    "refresh_hw_sysmon"
       "refresh_hw_target"             "refresh_hw_vio"                    "remove_hw_hbm_pc"
       "remove_hw_probe_enum"          "remove_hw_sio_link"                "remove_hw_sio_linkgroup"
       "remove_hw_sio_scan"            "remove_hw_sio_sweep"               "report_hw_axi_txn"
       "report_hw_ddrmc"               "report_hw_mig"                     "report_hw_targets"
       "reset_hw_axi"                  "reset_hw_ila"                      "reset_hw_vio_activity"
       "reset_hw_vio_outputs"          "resume_hw_hbm_amon"                "run_hw_axi"
       "run_hw_hbm_amon"               "run_hw_ila"                        "run_hw_sio_scan"
       "run_hw_sio_sweep"              "run_state_hw_jtag"                 "runtest_hw_jtag"
       "scan_dr_hw_jtag"               "scan_ir_hw_jtag"                   "set_hw_sysmon_reg"
       "stop_hw_hbm_amon"              "stop_hw_sio_scan"                  "stop_hw_sio_sweep"
       "update_hw_firmware"            "update_hw_gpio"                    "upload_hw_ila_data"
       "verify_hw_devices"             "wait_on_hw_ila"                    "wait_on_hw_sio_scan"
       "wait_on_hw_sio_sweep"          "write_hw_ila_data"                 "write_hw_sio_scan"
       "write_hw_sio_sweep"            "write_hw_svf"

       ;; IPFlow:
       "add_peripheral_interface"    "compile_c"                    "config_ip_cache"
       "convert_ips"                 "copy_ip"                      "create_ip"
       "create_ip_run"               "create_peripheral"            "delete_ip_run"
       "extract_files"               "generate_peripheral"          "generate_target"
       "get_ip_upgrade_results"      "get_ipdefs"                   "get_ips"
       "import_ip"                   "open_example_project"         "read_ip"
       "report_ip_status"            "reset_target"                 "synth_ip"
       "update_ip_catalog"           "update_module_reference"      "upgrade_ip"
       "validate_ip"                 "write_ip_tcl"                 "write_peripheral"

       ;; IPIntegrator:
       "apply_bd_automation"         "apply_board_connection"       "assign_bd_address"
       "close_bd_design"             "compile_c"                    "connect_bd_intf_net"
       "connect_bd_net"              "copy_bd_objs"                 "create_bd_addr_seg"
       "create_bd_cell"              "create_bd_design"             "create_bd_intf_net"
       "create_bd_intf_pin"          "create_bd_intf_port"          "create_bd_intf_tlm_port"
       "create_bd_net"               "create_bd_pin"                "create_bd_port"
       "create_bd_tlm_port"          "current_bd_design"            "current_bd_instance"
       "delete_bd_objs"              "disconnect_bd_intf_net"       "disconnect_bd_net"
       "exclude_bd_addr_seg"         "export_as_example_design"     "find_bd_objs"
       "generate_target"             "get_bd_addr_segs"             "get_bd_addr_spaces"
       "get_bd_cells"                "get_bd_designs"               "get_bd_intf_nets"
       "get_bd_intf_pins"            "get_bd_intf_ports"            "get_bd_nets"
       "get_bd_pins"                 "get_bd_ports"                 "get_bd_regs"
       "get_example_designs"         "get_template_bd_designs"      "group_bd_cells"
       "include_bd_addr_seg"         "instantiate_example_design"   "instantiate_template_bd_design"
       "make_bd_intf_pins_external"  "make_bd_pins_external"        "move_bd_cells"
       "open_bd_design"              "read_bd"                      "regenerate_bd_layout"
       "replace_bd_cell"             "report_bd_diffs"              "save_bd_design"
       "save_bd_design_as"           "ungroup_bd_cells"             "upgrade_bd_cells"
       "validate_bd_design"          "write_bd_tcl"

       ;; Memory:
       "implement_mig_cores"              "implement_xphy_cores"           "refresh_meminit"

       ;; Methodology:
       "create_waiver"                    "get_methodology_checks"         "get_methodology_violations"
       "report_methodology"               "reset_methodology"              "reset_methodology_check"

       ;; Netlist:
       "connect_net"                      "create_cell"                    "create_net"
       "create_pin"                       "disconnect_net"                 "get_net_delays"
       "remove_cell"                      "remove_net"                     "remove_pin"
       "rename_cell"                      "rename_net"                     "rename_pin"
       "rename_port"                      "rename_ref"                     "resize_net_bus"
       "resize_pin_bus"                   "tie_unused_pins"

       ;; Object:
       "add_drc_checks"                   "apply_board_connection"         "can_resolve_reference"
       "config_ip_cache"                  "create_drc_check"               "create_drc_ruledeck"
       "create_partition_def"             "create_pr_configuration"        "create_reconfig_module"
       "create_report_config"             "create_waiver"                  "current_board"
       "current_board_part"               "current_pr_configuration"       "delete_drc_check"
       "delete_drc_ruledeck"              "delete_hw_bitstream"            "delete_qor_suggestions"
       "delete_report_configs"            "delete_waivers"                 "filter"
       "find_routing_path"                "generate_reports"               "get_bel_pins"
       "get_bels"                         "get_board_bus_nets"             "get_board_buses"
       "get_board_component_interfaces"   "get_board_component_modes"      "get_board_component_pins"
       "get_board_components"             "get_board_interface_ports"      "get_board_ip_preferences"
       "get_board_jumpers"                "get_board_parameters"           "get_board_part_interfaces"
       "get_board_part_pins"              "get_board_parts"                "get_boards"
       "get_cdc_violations"               "get_cells"                      "get_cfgmem_parts"
       "get_clock_regions"                "get_clocks"                     "get_dashboard_gadgets"
       "get_debug_cores"                  "get_debug_ports"                "get_designs"
       "get_drc_checks"                   "get_drc_ruledecks"              "get_drc_violations"
       "get_files"                        "get_filesets"                   "get_generated_clocks"
       "get_highlighted_objects"          "get_hw_axi_txns"                "get_hw_axis"
       "get_hw_cfgmems"                   "get_hw_ddrmcs"                  "get_hw_devices"
       "get_hw_hbms"                      "get_hw_ila_datas"               "get_hw_ilas"
       "get_hw_migs"                      "get_hw_probes"                  "get_hw_servers"
       "get_hw_sio_commons"               "get_hw_sio_gtgroups"            "get_hw_sio_gts"
       "get_hw_sio_iberts"                "get_hw_sio_linkgroups"          "get_hw_sio_links"
       "get_hw_sio_plls"                  "get_hw_sio_rxs"                 "get_hw_sio_scans"
       "get_hw_sio_sweeps"                "get_hw_sio_txs"                 "get_hw_sysmons"
       "get_hw_targets"                   "get_hw_vios"                    "get_interfaces"
       "get_io_standards"                 "get_iobanks"                    "get_ip_upgrade_results"
       "get_ipdefs"                       "get_ips"                        "get_lib_cells"
       "get_lib_pins"                     "get_libs"                       "get_macros"
       "get_marked_objects"               "get_methodology_checks"         "get_methodology_violations"
       "get_net_delays"                   "get_nets"                       "get_nodes"
       "get_package_pins"                 "get_partition_defs"             "get_parts"
       "get_path_groups"                  "get_pblocks"                    "get_pins"
       "get_pips"                         "get_pkgpin_bytegroups"          "get_pkgpin_nibbles"
       "get_ports"                        "get_pr_configurations"          "get_primitives"
       "get_projects"                     "get_property"                   "get_qor_suggestions"
       "get_reconfig_modules"             "get_report_configs"             "get_runs"
       "get_selected_objects"             "get_site_pins"                  "get_site_pips"
       "get_sites"                        "get_slrs"                       "get_speed_models"
       "get_tiles"                        "get_timing_arcs"                "get_timing_paths"
       "get_waivers"                      "get_wires"                      "list_hw_samples"
       "list_property"                    "list_property_value"            "remove_drc_checks"
       "report_property"                  "report_qor_suggestions"         "report_waivers"
       "reset_drc_check"                  "reset_methodology_check"        "reset_property"
       "run_state_hw_jtag"                "runtest_hw_jtag"                "scan_dr_hw_jtag"
       "scan_ir_hw_jtag"                  "set_property"                   "write_ip_tcl"
       "write_waivers"

       ;; Partition:
       "create_partition_def"        "create_pr_configuration"     "create_reconfig_module"
       "current_pr_configuration"    "delete_partition_defs"       "delete_pr_configurations"
       "delete_reconfig_modules"     "get_partition_defs"          "get_pr_configurations"
       "get_reconfig_modules"        "setup_pr_configurations"

       ;; PinPlanning:
       "create_interface"            "create_port"                 "delete_interface"
       "make_diff_pair_ports"        "place_ports"                 "remove_port"
       "resize_port_bus"             "set_package_pin_val"         "split_diff_pair_ports"

       ;; Platform:
       "open_hw_platform"             "validate_hw_platform"         "write_hw_platform"
       "write_hw_platform_metadata"

       ;; Power:
       "delete_power_results"         "power_opt_design"             "read_saif"
       "report_power"                 "report_power_opt"             "reset_operating_conditions"
       "reset_switching_activity"     "set_operating_conditions"     "set_power_opt"
       "set_switching_activity"

       ;; Project:
       "add_files"                    "add_peripheral_interface"     "apply_board_connection"
       "archive_project"              "auto_detect_xpm"              "can_resolve_reference"
       "check_syntax"                 "close_design"                 "close_project"
       "compile_c"                    "copy_ip"                      "create_dashboard_gadget"
       "create_fileset"               "create_ip_run"                "create_peripheral"
       "create_project"               "create_run"                   "create_xps"
       "current_board_part"           "current_fileset"              "current_project"
       "current_run"                  "delete_dashboard_gadgets"     "delete_fileset"
       "delete_ip_run"                "delete_runs"                  "find_top"
       "generate_peripheral"          "generate_target"              "get_board_parts"
       "get_boards"                   "get_dashboard_gadgets"        "get_files"
       "get_filesets"                 "get_ip_upgrade_results"       "get_ips"
       "get_projects"                 "get_runs"                     "help"
       "import_files"                 "import_ip"                    "import_synplify"
       "import_xise"                  "import_xst"                   "launch_runs"
       "list_targets"                 "lock_design"                  "make_wrapper"
       "move_dashboard_gadget"        "move_files"                   "open_checkpoint"
       "open_example_project"         "open_io_design"               "open_project"
       "open_run"                     "refresh_design"               "refresh_meminit"
       "reimport_files"               "remove_files"                 "reorder_files"
       "report_compile_order"         "reset_project"                "reset_runs"
       "reset_target"                 "save_constraints"             "save_constraints_as"
       "save_project_as"              "set_part"                     "set_speed_grade"
       "synth_ip"                     "update_compile_order"         "update_design"
       "update_files"                 "update_sw_parameters"         "wait_on_run"
       "write_hwdef"                  "write_ip_tcl"                 "write_peripheral"

       ;; projutils:
       "convert_ngc"                  "copy_run"                     "create_rqs_run"
       "export_bd_synth"              "write_project_tcl"

       ;; PropertyAndParameter:
       "create_property"                 "filter"                          "get_param"
       "get_property"                    "list_param"                      "list_property"
       "list_property_value"             "report_param"                    "report_property"
       "reset_param"                     "reset_property"                  "set_param"
       "set_part"                        "set_property"

       ;; Report:
       "calc_config_time"                "check_timing"                    "create_drc_violation"
       "create_report_config"            "create_slack_histogram"          "delete_clock_networks_results"
       "delete_report_configs"           "delete_timing_results"           "delete_utilization_results"
       "generate_reports"                "get_msg_config"                  "get_pplocs"
       "get_report_configs"              "open_report"                     "report_bus_skew"
       "report_carry_chains"             "report_cdc"                      "report_clock_interaction"
       "report_clock_networks"           "report_clock_utilization"        "report_clocks"
       "report_config_implementation"    "report_config_timing"            "report_control_sets"
       "report_datasheet"                "report_debug_core"               "report_design_analysis"
       "report_disable_timing"           "report_drc"                      "report_environment"
       "report_exceptions"               "report_high_fanout_nets"         "report_hw_ddrmc"
       "report_hw_mig"                   "report_incremental_reuse"        "report_io"
       "report_methodology"              "report_operating_conditions"     "report_param"
       "report_phys_opt"                 "report_power"                    "report_pr_configuration_analysis"
       "report_property"                 "report_pulse_width"              "report_qor_assessment"
       "report_qor_suggestions"          "report_ram_utilization"          "report_route_status"
       "report_sim_device"               "report_ssn"                      "report_switching_activity"
       "report_synchronizer_mtbf"        "report_timing"                   "report_timing_summary"
       "report_transformed_primitives"   "report_utilization"              "report_waivers"
       "reset_drc"                       "reset_methodology"               "reset_msg_config"
       "reset_msg_count"                 "reset_ssn"                       "reset_timing"
       "set_msg_config"                  "version"

       ;; SDC:
       "all_clocks"                      "all_inputs"                      "all_outputs"
       "all_registers"                   "create_clock"                    "create_generated_clock"
       "current_design"                  "current_instance"                "get_cells"
       "get_clocks"                      "get_hierarchy_separator"         "get_nets"
       "get_pins"                        "get_ports"                       "group_path"
       "set_case_analysis"               "set_clock_groups"                "set_clock_latency"
       "set_clock_sense"                 "set_clock_uncertainty"           "set_data_check"
       "set_disable_timing"              "set_false_path"                  "set_hierarchy_separator"
       "set_input_delay"                 "set_load"                        "set_logic_dc"
       "set_logic_one"                   "set_logic_zero"                  "set_max_delay"
       "set_max_time_borrow"             "set_min_delay"                   "set_multicycle_path"
       "set_operating_conditions"        "set_output_delay"                "set_propagated_clock"
       "set_units"

       ;; Simulation:
       "add_bp"                      "add_condition"                "add_files"
       "add_force"                   "checkpoint_vcd"               "close_saif"
       "close_sim"                   "close_vcd"                    "compile_simlib"
       "config_compile_simlib"       "create_fileset"               "current_frame"
       "current_scope"               "current_sim"                  "current_time"
       "current_vcd"                 "delete_fileset"               "describe"
       "export_ip_user_files"        "export_simulation"            "flush_vcd"
       "generate_mem_files"          "get_objects"                  "get_scopes"
       "get_simulators"              "get_stacks"                   "get_value"
       "import_files"                "launch_simulation"            "limit_vcd"
       "log_saif"                    "log_vcd"                      "log_wave"
       "ltrace"                      "move_files"                   "open_saif"
       "open_vcd"                    "open_wave_database"           "ptrace"
       "read_saif"                   "relaunch_sim"                 "remove_bps"
       "remove_conditions"           "remove_files"                 "remove_forces"
       "report_bps"                  "report_conditions"            "report_drivers"
       "report_frames"               "report_objects"               "report_scopes"
       "report_simlib_info"          "report_stacks"                "report_values"
       "reset_simulation"            "restart"                      "run"
       "set_value"                   "setup_ip_static_library"      "start_vcd"
       "step"                        "stop"                         "stop_vcd"
       "write_sdf"                   "write_verilog"                "write_vhdl"
       "xsim"

       ;; SysGen:
       "create_sysgen"               "make_wrapper"

       ;; Timing:
       "check_timing"                 "config_design_analysis"        "config_timing_analysis"
       "config_timing_corners"        "create_slack_histogram"        "delete_qor_suggestions"
       "delete_timing_results"        "get_net_delays"                "get_qor_suggestions"
       "get_timing_arcs"              "get_timing_paths"              "read_qor_suggestions"
       "report_bus_skew"              "report_cdc"                    "report_clock_interaction"
       "report_clock_networks"        "report_clock_utilization"      "report_clocks"
       "report_config_timing"         "report_datasheet"              "report_design_analysis"
       "report_disable_timing"        "report_drc"                    "report_exceptions"
       "report_high_fanout_nets"      "report_methodology"            "report_pulse_width"
       "report_qor_assessment"        "report_qor_suggestions"        "report_synchronizer_mtbf"
       "report_timing"                "report_timing_summary"         "reset_timing"
       "set_delay_model"              "set_disable_timing"            "set_external_delay"
       "update_timing"                "write_inferred_xdc"            "write_qor_suggestions"
       "write_sdf"                    "write_xdc"

       ;; ToolLaunch:
       "get_simulators"               "launch_chipscope_analyzer"     "launch_impact"
       "launch_simulation"

       ;; Tools:
       "iphys_opt_design"             "link_design"                   "list_features"
       "load_features"                "opt_design"                    "phys_opt_design"
       "place_design"                 "read_iphys_opt_tcl"            "register_proc"
       "report_pipeline_analysis"     "route_design"                  "synth_design"
       "unregister_proc"              "update_clock_routing"          "update_noc_qos"
       "write_iphys_opt_tcl"

       ;; Vitis:
       "open_hw_platform"             "validate_hw_platform"          "write_hw_platform"
       "write_hw_platform_metadata"

       ;; Waiver:
       "create_waiver"                "delete_waivers"                "get_waivers"
       "report_waivers"               "write_waivers"

       ;; Waveform:
       "add_wave"                     "add_wave_divider"              "add_wave_group"
       "add_wave_marker"              "add_wave_virtual_bus"          "close_wave_config"
       "create_wave_config"           "current_wave_config"           "get_wave_configs"
       "get_waves"                    "move_wave"                     "open_wave_config"
       "remove_wave"                  "save_wave_config"              "select_wave_objects"

       ;; XDC:
       "add_cells_to_pblock"          "all_clocks"                    "all_cpus"
       "all_dsps"                     "all_fanin"                     "all_fanout"
       "all_ffs"                      "all_hsios"                     "all_inputs"
       "all_latches"                  "all_outputs"                   "all_rams"
       "all_registers"                "connect_debug_cores"           "connect_debug_port"
       "create_clock"                 "create_debug_core"             "create_debug_port"
       "create_generated_clock"       "create_macro"                  "create_pblock"
       "create_property"              "create_waiver"                 "current_design"
       "current_instance"             "delete_macros"                 "delete_pblocks"
       "filter"                       "get_bel_pins"                  "get_bels"
       "get_cells"                    "get_clocks"                    "get_debug_cores"
       "get_debug_ports"              "get_generated_clocks"          "get_hierarchy_separator"
       "get_iobanks"                  "get_macros"                    "get_nets"
       "get_nodes"                    "get_package_pins"              "get_path_groups"
       "get_pblocks"                  "get_pins"                      "get_pips"
       "get_pkgpin_bytegroups"        "get_pkgpin_nibbles"            "get_ports"
       "get_property"                 "get_site_pins"                 "get_site_pips"
       "get_sites"                    "get_slrs"                      "get_speed_models"
       "get_tiles"                    "get_timing_arcs"               "get_wires"
       "group_path"                   "make_diff_pair_ports"          "remove_cells_from_pblock"
       "reset_operating_conditions"   "reset_switching_activity"      "resize_pblock"
       "set_bus_skew"                 "set_case_analysis"             "set_clock_groups"
       "set_clock_latency"            "set_clock_sense"               "set_clock_uncertainty"
       "set_data_check"               "set_disable_timing"            "set_external_delay"
       "set_false_path"               "set_hierarchy_separator"       "set_input_delay"
       "set_input_jitter"             "set_load"                      "set_logic_dc"
       "set_logic_one"                "set_logic_unconnected"         "set_logic_zero"
       "set_max_delay"                "set_max_time_borrow"           "set_min_delay"
       "set_multicycle_path"          "set_operating_conditions"      "set_output_delay"
       "set_package_pin_val"          "set_power_opt"                 "set_propagated_clock"
       "set_property"                 "set_switching_activity"        "set_system_jitter"
       "set_units"                    "update_macro"

       ;; xilinxtclstore:
       "convert_ngc"                  "copy_run"                     "create_rqs_run"
       "export_bd_synth"              "export_ip_user_files"         "export_simulation"
       "setup_ip_static_library"      "write_project_tcl"
       ))



(defun larumbe/vivado-shell-completion-at-point ()
  "Used as an element of `completion-at-point-functions'."
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
         (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
         (str (buffer-substring b e))
         (allcomp (all-completions str larumbe/vivado-tcl-commands)))
    (list b e allcomp)))


(defun larumbe/vivado-shell-send-exit-command ()
  (interactive)
  "Send 'exit' command to quit Vivado console."
  (let ((proc (get-buffer-process larumbe/vivado-tcl-shell-buffer)))
    (comint-send-string proc "exit")
    (comint-send-string proc "\n")))


(define-minor-mode larumbe/vivado-shell-completion-at-point-mode
  "Add extensions for Xilinx Vivado TCL shell.
Autocompletion based on `vivado' package keywords. "
  :keymap
  '(("\C-d" . larumbe/vivado-shell-send-exit-command)) ; Should override `comint-delchar-or-maybe-eof'
  (when (not (equal (buffer-name (current-buffer)) larumbe/vivado-tcl-shell-buffer))
    (error "Not in Vivado shell buffer!"))
  (make-local-variable 'comint-dynamic-complete-functions) ; Use this variable instead of `completion-at-point-functions' to preserve file-name expansion
  (if larumbe/vivado-shell-completion-at-point-mode
      ;; INFO: It seems that without appending, the `larumbe/vivado-shell-completion-at-point' will have precedence
      ;; over other functions present in `comint-dynamic-complete-functions'
      (add-to-list 'comint-dynamic-complete-functions #'larumbe/vivado-shell-completion-at-point)
    (delete #'larumbe/vivado-shell-completion-at-point comint-dynamic-complete-functions)))


;; Fake TCL Shell based on compilation/comint modes to allow for regexps
;; Advantages over `inferior-tcl': Can parse Regexps
;; Drawbacks over `inferior-tcl': Requires custom function to send lines/regions from a .tcl buffer
;;   - This would be previous function :)
(defun larumbe/vivado-shell ()
  "Invoke a TCL vivado shell with the proper regexps, suited for compilation"
  (interactive)
  (let ((command (concat tcl-application " " (mapconcat 'identity tcl-command-switches " ")))
        (bufname larumbe/vivado-tcl-shell-buffer)
        (parser  "vivado"))
    (larumbe/compilation-interactive command bufname parser)
    (larumbe/vivado-shell-completion-at-point-mode 1)
    (company-mode 1)))


;; Same as `larumbe/tcl-send-line-or-region-and-step'  but intended for sending text to a *compilation* Vivado Shell with regexps
(defun larumbe/vivado-shell-tcl-send-line-or-region-and-step ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (get-buffer-process larumbe/vivado-tcl-shell-buffer)))
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (comint-send-string proc (buffer-substring-no-properties from to))
    (comint-send-string proc "\n")
    (goto-char end)))



;;; Vivado XDC
(defvar larumbe/vivado-tcl-xdc-commands
      '(
        ;; Fetched from `larumbe/vivado-tcl-commands' XDC commands
        "add_cells_to_pblock"          "all_clocks"                    "all_cpus"
        "all_dsps"                     "all_fanin"                     "all_fanout"
        "all_ffs"                      "all_hsios"                     "all_inputs"
        "all_latches"                  "all_outputs"                   "all_rams"
        "all_registers"                "connect_debug_cores"           "connect_debug_port"
        "create_clock"                 "create_debug_core"             "create_debug_port"
        "create_generated_clock"       "create_macro"                  "create_pblock"
        "create_property"              "create_waiver"                 "current_design"
        "current_instance"             "delete_macros"                 "delete_pblocks"
        "filter"                       "get_bel_pins"                  "get_bels"
        "get_cells"                    "get_clocks"                    "get_debug_cores"
        "get_debug_ports"              "get_generated_clocks"          "get_hierarchy_separator"
        "get_iobanks"                  "get_macros"                    "get_nets"
        "get_nodes"                    "get_package_pins"              "get_path_groups"
        "get_pblocks"                  "get_pins"                      "get_pips"
        "get_pkgpin_bytegroups"        "get_pkgpin_nibbles"            "get_ports"
        "get_property"                 "get_site_pins"                 "get_site_pips"
        "get_sites"                    "get_slrs"                      "get_speed_models"
        "get_tiles"                    "get_timing_arcs"               "get_wires"
        "group_path"                   "make_diff_pair_ports"          "remove_cells_from_pblock"
        "reset_operating_conditions"   "reset_switching_activity"      "resize_pblock"
        "set_bus_skew"                 "set_case_analysis"             "set_clock_groups"
        "set_clock_latency"            "set_clock_sense"               "set_clock_uncertainty"
        "set_data_check"               "set_disable_timing"            "set_external_delay"
        "set_false_path"               "set_hierarchy_separator"       "set_input_delay"
        "set_input_jitter"             "set_load"                      "set_logic_dc"
        "set_logic_one"                "set_logic_unconnected"         "set_logic_zero"
        "set_max_delay"                "set_max_time_borrow"           "set_min_delay"
        "set_multicycle_path"          "set_operating_conditions"      "set_output_delay"
        "set_package_pin_val"          "set_power_opt"                 "set_propagated_clock"
        "set_property"                 "set_switching_activity"        "set_system_jitter"
        "set_units"                    "update_macro"
        ))


(defvar larumbe/vivado-tcl-xdc-properties
      '(
        "CLOCK_DEDICATED_ROUTE" "IOSTANDARD" "DRIVE" "DIFF_TERM" "VCCAUX_IO" "SLEW" "FAST" "DCI_CASCADE"
        "PACKAGE_PIN" "IOB" "LOC"
        "PROHIBIT"
        "BITSTREAM.CONFIG.UNUSEDPIN" "BITSTREAM.GENERAL.COMPRESS" ; Add more options...
        ))

(defvar larumbe/vivado-tcl-xdc-switches
      '(
        "name" "period" "clock" "through" "filter" "hierarchical" "hier" "fall_from" "rise_from" "add_delay"
        "max" "min" "rise_to" "fall_to" "of_objects" "from" "to" "setup" "hold" "end" "start" "of" "group"
        "physically_exclusive" "asynchronous" "min" "rise_to" "fall_to" "of_objects" "from" "to" "setup" "hold" "of" "group" "asynchronous"
        "include_generated_clocks" "primitive_group" "pppasynchronous"
        "intf_net" "dict" "range" "offset" "dir" "type" "vlnv" "net"
        ))


(defvar larumbe/vivado-tcl-xdc-commands-font-lock   (regexp-opt larumbe/vivado-tcl-xdc-commands 'symbols))
(defvar larumbe/vivado-tcl-xdc-properties-font-lock (regexp-opt larumbe/vivado-tcl-xdc-properties 'symbols))
(defvar larumbe/vivado-tcl-xdc-switches-font-lock   (concat "-" (regexp-opt larumbe/vivado-tcl-xdc-switches 'symbols)))


(defvar larumbe/vivado-tcl-xdc-font-lock
      (list
       (list larumbe/vivado-tcl-xdc-commands-font-lock   0 font-lock-keyword-face)
       (list larumbe/vivado-tcl-xdc-properties-font-lock 0 font-lock-constant-face)
       (list larumbe/vivado-tcl-xdc-switches-font-lock   0 font-lock-constant-face)
       ))


(defun larumbe/vivado-tcl-xdc-completion-at-point ()
  "Used as an element of `completion-at-point-functions'."
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
         (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
         (str (buffer-substring b e))
         (allcomp (all-completions str larumbe/vivado-tcl-xdc-commands)))
    (list b e allcomp)))


(define-derived-mode vivado-xdc-mode tcl-mode
  (font-lock-add-keywords 'vivado-xdc-mode larumbe/vivado-tcl-xdc-font-lock) ; Modified to preserve tcl-keywords
  (make-local-variable 'completion-at-point-functions)
  (add-to-list 'completion-at-point-functions 'larumbe/vivado-tcl-xdc-completion-at-point)
  (setq mode-name "XDC"))



(provide 'vivado-utils)

;;; vivado-utils.el ends here
