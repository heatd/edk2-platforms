#
#  Copyright (c) 2018 - 2024, Arm Limited. All rights reserved.
#  (C) Copyright 2021 Hewlett Packard Enterprise Development LP<BR>
#
#  SPDX-License-Identifier: BSD-2-Clause-Patent
#

!include Platform/ARM/VExpressPkg/ArmVExpress.dsc.inc

[Defines]
  # To allow the use of secure storage, set this to TRUE.
  DEFINE SECURE_STORAGE_ENABLE              = FALSE

  # To allow the use of UEFI secure boot, set this to TRUE.
  # Secure boot requires secure storage to be enabled as well.
  DEFINE SECURE_BOOT_ENABLE                 = FALSE

  # To allow HDLCD display using the Graphics Output Protocol, set this to TRUE.
  DEFINE ENABLE_GOP                         = FALSE

  # To enable LPI and CPPC power management functionality, set this to TRUE.
  DEFINE LPI_EN                             = FALSE
  DEFINE CPPC_EN                            = FALSE

[BuildOptions]
  # EDK2_PLAT_FW_REL_VERSION macro resolve to value like RD-INFRA-2024.09.30.
  # This value is set in build-uefi.sh
  *_*_*_CC_FLAGS = -DDISABLE_NEW_DEPRECATED_INTERFACES -DEDK2_PLAT_FW_REL_VERSION=\"$(EDK2_PLAT_FW_REL_VERSION)\"

[LibraryClasses.common]
  ArmLib|ArmPkg/Library/ArmLib/ArmBaseLib.inf
  ArmMmuLib|ArmPkg/Library/ArmMmuLib/ArmMmuBaseLib.inf
  ArmSmcLib|MdePkg/Library/ArmSmcLib/ArmSmcLib.inf
  ArmSvcLib|MdePkg/Library/ArmSvcLib/ArmSvcLib.inf
  ArmPlatformSysConfigLib|Platform/ARM/VExpressPkg/Library/ArmVExpressSysConfigLib/ArmVExpressSysConfigLib.inf
  ArmPlatformLib|Platform/ARM/SgiPkg/Library/PlatformLib/PlatformLib.inf
  BasePathLib|ShellPkg/Library/UefiShellLib/UefiShellLib.inf
  LcdHwLib|ArmPlatformPkg/Library/HdLcd/HdLcd.inf
  LcdPlatformLib|Platform/ARM/SgiPkg/Library/HdLcdArmSgiLib/HdLcdArmSgiLib.inf
  NorFlashDeviceLib|Platform/ARM/Library/P30NorFlashDeviceLib/P30NorFlashDeviceLib.inf
  NorFlashPlatformLib|Platform/ARM/SgiPkg/Library/NorFlashLib/NorFlashLib.inf
  # NOR flash identification support
  NorFlashInfoLib|EmbeddedPkg/Library/NorFlashInfoLib/NorFlashInfoLib.inf
  HobLib|MdePkg/Library/DxeHobLib/DxeHobLib.inf
  ResetSystemLib|ArmPkg/Library/ArmPsciResetSystemLib/ArmPsciResetSystemLib.inf
  ArmMonitorLib|ArmPkg/Library/ArmMonitorLib/ArmMonitorLib.inf
  TimerLib|ArmPkg/Library/ArmArchTimerLib/ArmArchTimerLib.inf
  MmUnblockMemoryLib|MdePkg/Library/MmUnblockMemoryLib/MmUnblockMemoryLibNull.inf

  # Virtio Support
  VirtioLib|OvmfPkg/Library/VirtioLib/VirtioLib.inf
  VirtioMmioDeviceLib|OvmfPkg/Library/VirtioMmioDeviceLib/VirtioMmioDeviceLib.inf
  FileExplorerLib|MdeModulePkg/Library/FileExplorerLib/FileExplorerLib.inf
  OrderedCollectionLib|MdePkg/Library/BaseOrderedCollectionRedBlackTreeLib/BaseOrderedCollectionRedBlackTreeLib.inf

[LibraryClasses.common.SEC]
  HobLib|MdePkg/Library/PeiHobLib/PeiHobLib.inf
  MemoryAllocationLib|MdePkg/Library/PeiMemoryAllocationLib/PeiMemoryAllocationLib.inf
  PcdLib|MdePkg/Library/BasePcdLibNull/BasePcdLibNull.inf
  PeiServicesLib|MdePkg/Library/PeiServicesLib/PeiServicesLib.inf
  PeiServicesTablePointerLib|ArmPkg/Library/PeiServicesTablePointerLib/PeiServicesTablePointerLib.inf

[LibraryClasses.common.PEI_CORE, LibraryClasses.common.PEIM]
  BaseMemoryLib|MdePkg/Library/BaseMemoryLib/BaseMemoryLib.inf
  HobLib|MdePkg/Library/PeiHobLib/PeiHobLib.inf
  MemoryAllocationLib|MdePkg/Library/PeiMemoryAllocationLib/PeiMemoryAllocationLib.inf
  PcdLib|MdePkg/Library/PeiPcdLib/PeiPcdLib.inf
  PeiServicesLib|MdePkg/Library/PeiServicesLib/PeiServicesLib.inf
  PeiServicesTablePointerLib|ArmPkg/Library/PeiServicesTablePointerLib/PeiServicesTablePointerLib.inf
  ReportStatusCodeLib|MdePkg/Library/BaseReportStatusCodeLibNull/BaseReportStatusCodeLibNull.inf

[LibraryClasses.common.PEI_CORE]
  PeiCoreEntryPoint|MdePkg/Library/PeiCoreEntryPoint/PeiCoreEntryPoint.inf

[LibraryClasses.common.PEIM]
  ArmFfaLib|MdeModulePkg/Library/ArmFfaLib/ArmFfaPeiLib.inf
  PeimEntryPoint|MdePkg/Library/PeimEntryPoint/PeimEntryPoint.inf

[LibraryClasses.common.DXE_CORE]
  DxeCoreEntryPoint|MdePkg/Library/DxeCoreEntryPoint/DxeCoreEntryPoint.inf
  HobLib|MdePkg/Library/DxeCoreHobLib/DxeCoreHobLib.inf
  MemoryAllocationLib|MdeModulePkg/Library/DxeCoreMemoryAllocationLib/DxeCoreMemoryAllocationLib.inf
  PcdLib|MdePkg/Library/BasePcdLibNull/BasePcdLibNull.inf
  PrintLib|MdePkg/Library/BasePrintLib/BasePrintLib.inf

[LibraryClasses.common.DXE_DRIVER]
  ArmFfaLib|MdeModulePkg/Library/ArmFfaLib/ArmFfaDxeLib.inf
  PciHostBridgeLib|Platform/ARM/SgiPkg/Library/PciHostBridgeLib/PciHostBridgeLib.inf
  PciSegmentLib|MdePkg/Library/BasePciSegmentLibPci/BasePciSegmentLibPci.inf
  PciLib|MdePkg/Library/BasePciLibPciExpress/BasePciLibPciExpress.inf
  PciExpressLib|MdePkg/Library/BasePciExpressLib/BasePciExpressLib.inf

[LibraryClasses.common.DXE_RUNTIME_DRIVER]
  ArmFfaLib|MdeModulePkg/Library/ArmFfaLib/ArmFfaDxeLib.inf
  BaseMemoryLib|MdePkg/Library/BaseMemoryLib/BaseMemoryLib.inf
  HobLib|MdePkg/Library/DxeHobLib/DxeHobLib.inf
!if $(TARGET) != RELEASE
  DebugLib|MdePkg/Library/DxeRuntimeDebugLibSerialPort/DxeRuntimeDebugLibSerialPort.inf
!endif

[LibraryClasses.common.UEFI_DRIVER, LibraryClasses.common.UEFI_APPLICATION, LibraryClasses.common.DXE_RUNTIME_DRIVER, LibraryClasses.common.DXE_DRIVER]
  ArmFfaLib|MdeModulePkg/Library/ArmFfaLib/ArmFfaDxeLib.inf
  PcdLib|MdePkg/Library/DxePcdLib/DxePcdLib.inf

################################################################################
#
# Pcd Section - list of all EDK II PCD Entries defined by this Platform
#
################################################################################

[PcdsFeatureFlag.common]
  gArmSgiTokenSpaceGuid.PcdVirtioBlkSupported|TRUE
  gArmSgiTokenSpaceGuid.PcdVirtioNetSupported|TRUE
  gEfiMdeModulePkgTokenSpaceGuid.PcdEnableVariableRuntimeCache|FALSE

!if $(PCIE_ENABLE) == TRUE
  gArmSgiTokenSpaceGuid.PcdPcieEnable|TRUE
!endif

[PcdsFixedAtBuild.common]
  gEfiMdeModulePkgTokenSpaceGuid.PcdMaxVariableSize|0x2000

  # DRAM Block2 Base and Size
  gArmSgiTokenSpaceGuid.PcdDramBlock2Base|0x8080000000
  gArmSgiTokenSpaceGuid.PcdDramBlock2Size|0x180000000

!if $(LPI_EN) == TRUE
  # Allow use of LPI in the response to _OSC method call
  gArmSgiTokenSpaceGuid.PcdOscLpiEnable|1
!endif

!if $(CPPC_EN) == TRUE
  # Allow use of CPPC in the response to _OSC method call
  gArmSgiTokenSpaceGuid.PcdOscCppcEnable|1
!endif

  # NV Storage PCDs.
  gEfiMdeModulePkgTokenSpaceGuid.PcdFlashNvStorageVariableSize|0x01400000
  gEfiMdeModulePkgTokenSpaceGuid.PcdFlashNvStorageFtwWorkingSize|0x01400000
  gEfiMdeModulePkgTokenSpaceGuid.PcdFlashNvStorageFtwSpareSize|0x01400000

  gArmPlatformTokenSpaceGuid.PcdCPUCoresStackBase|0x80000000
  gArmPlatformTokenSpaceGuid.PcdCPUCorePrimaryStackSize|0x40000

  # ACPI Table Version
  gEfiMdeModulePkgTokenSpaceGuid.PcdAcpiExposedTableVersions|0x20

  # SMBIOS entry point version
  gEfiMdeModulePkgTokenSpaceGuid.PcdSmbiosVersion|0x0304
  gEfiMdeModulePkgTokenSpaceGuid.PcdSmbiosDocRev|0x0

  #
  # PCIe
  #
  gArmTokenSpaceGuid.PcdPciBusMin|0
  gArmTokenSpaceGuid.PcdPciBusMax|255
  gArmTokenSpaceGuid.PcdPciIoBase|0x0
  gArmTokenSpaceGuid.PcdPciIoSize|0x00800000
  gEfiMdePkgTokenSpaceGuid.PcdPciIoTranslation|0x77800000
  gEfiMdePkgTokenSpaceGuid.PcdPciMmio32Translation|0x0
  gEfiMdePkgTokenSpaceGuid.PcdPciMmio64Translation|0x0
  gEmbeddedTokenSpaceGuid.PcdPrePiCpuIoSize|24

  ## PL011 - Serial Terminal
  gEfiMdeModulePkgTokenSpaceGuid.PcdSerialRegisterBase|0x2A400000
  gEfiMdePkgTokenSpaceGuid.PcdUartDefaultBaudRate|115200
  gEfiMdePkgTokenSpaceGuid.PcdUartDefaultReceiveFifoDepth|0
  gArmPlatformTokenSpaceGuid.PL011UartInteger|4
  gArmPlatformTokenSpaceGuid.PL011UartFractional|0

  ## PL370 - HDLCD1
  gArmPlatformTokenSpaceGuid.PcdArmHdLcdBase|0x7FF60000

  ## PL011 - Serial Debug UART
  gArmPlatformTokenSpaceGuid.PcdSerialDbgUartClkInHz|7372800
  gArmPlatformTokenSpaceGuid.PcdSerialDbgUartBaudRate|115200


  # List of Device Paths that support BootMonFs
  gArmBootMonFsTokenSpaceGuid.PcdBootMonFsSupportedDevicePaths|L"VenHw(DE6AE758-D662-4E17-A97C-4C5964DA4C41,00)"

  # ARM OS Loader
  gEfiMdePkgTokenSpaceGuid.PcdPlatformBootTimeOut|3

  gEmbeddedTokenSpaceGuid.PcdMetronomeTickPeriod|1000
  gEmbeddedTokenSpaceGuid.PcdTimerPeriod|1000

  # Virtio Disk
  gArmSgiTokenSpaceGuid.PcdVirtioBlkSize|0x10000

  # Ethernet / Virtio Network
  gArmSgiTokenSpaceGuid.PcdVirtioNetSize|0x10000

  # Counter, Timer and Watchdog
  gArmSgiTokenSpaceGuid.PcdTimerBase0Base|0x2A830000
  gArmSgiTokenSpaceGuid.PcdTimerBase0Size|0x00010000
  gArmSgiTokenSpaceGuid.PcdTimerControlBase|0x2A810000
  gArmSgiTokenSpaceGuid.PcdTimerControlSize|0x00010000
  gArmSgiTokenSpaceGuid.PcdTimerCounterReadBase|0x2A800000
  gArmSgiTokenSpaceGuid.PcdTimerCounterReadSize|0x00010000
  gArmSgiTokenSpaceGuid.PcdWdogBase|0x2A440000
  gArmSgiTokenSpaceGuid.PcdWdogSize|0x00020000

  #
  # Set the base address and size of the buffer used
  # for communication between the Normal world edk2
  # with StandaloneMm image at S-EL0 through MM_COMMUNICATE.
  # This buffer gets allocated in ATF and since we do not have
  # a mechanism currently to communicate the base address and
  # size of this buffer from ATF, hard-code it here
  #
  ## MM Communicate
  gArmTokenSpaceGuid.PcdMmBufferBase|0xFF600000
  gArmTokenSpaceGuid.PcdMmBufferSize|0x10000

################################################################################
#
# Components Section - list of all EDK II Modules needed by this Platform
#
################################################################################
[Components.common]
  #
  # PEI Phase modules
  #
  ArmPkg/Drivers/CpuPei/CpuPei.inf
  ArmPlatformPkg/MemoryInitPei/MemoryInitPeim.inf
  ArmPlatformPkg/Sec/Sec.inf
  ArmPlatformPkg/PlatformPei/PlatformPeim.inf
  MdeModulePkg/Core/Pei/PeiMain.inf
  MdeModulePkg/Universal/PCD/Pei/Pcd.inf {
    <LibraryClasses>
      PcdLib|MdePkg/Library/BasePcdLibNull/BasePcdLibNull.inf
  }
  MdeModulePkg/Universal/FaultTolerantWritePei/FaultTolerantWritePei.inf
  MdeModulePkg/Universal/Variable/Pei/VariablePei.inf
  MdeModulePkg/Core/DxeIplPeim/DxeIpl.inf {
    <LibraryClasses>
      NULL|MdeModulePkg/Library/LzmaCustomDecompressLib/LzmaCustomDecompressLib.inf
  }
  Platform/ARM/SgiPkg/Library/SgiPlatformPei/SgiPlatformPei.inf {
    <LibraryClasses>
      FdtLib|MdePkg/Library/BaseFdtLib/BaseFdtLib.inf
  }

  #
  # DXE
  #
  MdeModulePkg/Core/Dxe/DxeMain.inf {
    <LibraryClasses>
      NULL|MdeModulePkg/Library/DxeCrc32GuidedSectionExtractLib/DxeCrc32GuidedSectionExtractLib.inf
    <PcdsFixedAtBuild>
      gEfiMdePkgTokenSpaceGuid.PcdDebugPrintErrorLevel|0x8000000F
  }

  #
  # Architectural Protocols
  #
  ArmPkg/Drivers/CpuDxe/CpuDxe.inf
  ArmPkg/Drivers/ArmGicDxe/ArmGicV3Dxe.inf
  ArmPkg/Drivers/TimerDxe/TimerDxe.inf
  ArmPkg/Drivers/GenericWatchdogDxe/GenericWatchdogDxe.inf
!if $(ENABLE_GOP) == TRUE
  ArmPlatformPkg/Drivers/LcdGraphicsOutputDxe/LcdGraphicsOutputDxe.inf
!endif
  Platform/ARM/Drivers/NorFlashDxe/NorFlashDxe.inf
  EmbeddedPkg/RealTimeClockRuntimeDxe/RealTimeClockRuntimeDxe.inf
  EmbeddedPkg/MetronomeDxe/MetronomeDxe.inf
  MdeModulePkg/Core/RuntimeDxe/RuntimeDxe.inf
  MdeModulePkg/Universal/CapsuleRuntimeDxe/CapsuleRuntimeDxe.inf
  MdeModulePkg/Universal/MonotonicCounterRuntimeDxe/MonotonicCounterRuntimeDxe.inf
  MdeModulePkg/Universal/ResetSystemRuntimeDxe/ResetSystemRuntimeDxe.inf
!if $(SECURE_BOOT_ENABLE) == TRUE
  MdeModulePkg/Universal/SecurityStubDxe/SecurityStubDxe.inf {
    <LibraryClasses>
      NULL|SecurityPkg/Library/DxeImageVerificationLib/DxeImageVerificationLib.inf
  }
  SecurityPkg/VariableAuthenticated/SecureBootConfigDxe/SecureBootConfigDxe.inf
!else
  MdeModulePkg/Universal/SecurityStubDxe/SecurityStubDxe.inf
!endif
  OvmfPkg/VirtioBlkDxe/VirtioBlk.inf

  MdeModulePkg/Universal/Console/ConPlatformDxe/ConPlatformDxe.inf
  MdeModulePkg/Universal/Console/ConSplitterDxe/ConSplitterDxe.inf
  MdeModulePkg/Universal/Console/GraphicsConsoleDxe/GraphicsConsoleDxe.inf
  MdeModulePkg/Universal/Console/TerminalDxe/TerminalDxe.inf
  MdeModulePkg/Universal/SerialDxe/SerialDxe.inf
!if $(SECURE_STORAGE_ENABLE) == TRUE
  MdeModulePkg/Universal/Variable/RuntimeDxe/VariableSmmRuntimeDxe.inf
!else
  MdeModulePkg/Universal/Variable/RuntimeDxe/VariableRuntimeDxe.inf {
    <LibraryClasses>
      NULL|MdeModulePkg/Library/VarCheckUefiLib/VarCheckUefiLib.inf
      NULL|EmbeddedPkg/Library/NvVarStoreFormattedLib/NvVarStoreFormattedLib.inf
      BaseMemoryLib|MdePkg/Library/BaseMemoryLib/BaseMemoryLib.inf
  }
  MdeModulePkg/Universal/FaultTolerantWriteDxe/FaultTolerantWriteDxe.inf
!endif

  #
  # ACPI Support
  #
  MdeModulePkg/Universal/Acpi/AcpiTableDxe/AcpiTableDxe.inf
  MdeModulePkg/Universal/HiiDatabaseDxe/HiiDatabaseDxe.inf

  #
  # SMBIOS/DMI
  #
  MdeModulePkg/Universal/SmbiosDxe/SmbiosDxe.inf
  Platform/ARM/SgiPkg/Drivers/SmbiosPlatformDxe/SmbiosPlatformDxe.inf

  #
  # platform driver
  #
  Platform/ARM/SgiPkg/Drivers/PlatformDxe/PlatformDxe.inf

  #
  # FAT filesystem + GPT/MBR partitioning
  #
  MdeModulePkg/Universal/Disk/DiskIoDxe/DiskIoDxe.inf
  MdeModulePkg/Universal/Disk/PartitionDxe/PartitionDxe.inf
  MdeModulePkg/Universal/Disk/UnicodeCollation/EnglishDxe/EnglishDxe.inf
  FatPkg/EnhancedFatDxe/Fat.inf

  #
  # Bds
  #
  MdeModulePkg/Universal/BootManagerPolicyDxe/BootManagerPolicyDxe.inf
  MdeModulePkg/Universal/BdsDxe/BdsDxe.inf
  MdeModulePkg/Universal/DevicePathDxe/DevicePathDxe.inf
  MdeModulePkg/Universal/DisplayEngineDxe/DisplayEngineDxe.inf
  MdeModulePkg/Universal/SetupBrowserDxe/SetupBrowserDxe.inf
  MdeModulePkg/Application/UiApp/UiApp.inf {
    <LibraryClasses>
      NULL|MdeModulePkg/Library/BootDiscoveryPolicyUiLib/BootDiscoveryPolicyUiLib.inf
      NULL|MdeModulePkg/Library/DeviceManagerUiLib/DeviceManagerUiLib.inf
      NULL|MdeModulePkg/Library/BootManagerUiLib/BootManagerUiLib.inf
      NULL|MdeModulePkg/Library/BootMaintenanceManagerUiLib/BootMaintenanceManagerUiLib.inf
      PcdLib|MdePkg/Library/DxePcdLib/DxePcdLib.inf
  }

  # Virtio Network
  OvmfPkg/VirtioNetDxe/VirtioNet.inf

!if $(PCIE_ENABLE) == TRUE
  #
  # Required by PCI
  #
  ArmPkg/Drivers/ArmPciCpuIo2Dxe/ArmPciCpuIo2Dxe.inf

  #
  # PCI Support
  #
  MdeModulePkg/Bus/Pci/PciBusDxe/PciBusDxe.inf
  MdeModulePkg/Bus/Pci/PciHostBridgeDxe/PciHostBridgeDxe.inf {
    <PcdsFixedAtBuild>
      gEfiMdePkgTokenSpaceGuid.PcdDebugPrintErrorLevel|0x8010004F
  }
!endif

  #
  # AHCI Support
  #
  MdeModulePkg/Bus/Ata/AtaAtapiPassThru/AtaAtapiPassThru.inf
  MdeModulePkg/Bus/Ata/AtaBusDxe/AtaBusDxe.inf

  #
  # SATA Controller
  #
  MdeModulePkg/Bus/Pci/SataControllerDxe/SataControllerDxe.inf

!if $(SECURE_STORAGE_ENABLE) == TRUE
  ArmPkg/Drivers/MmCommunicationDxe/MmCommunication.inf {
    <LibraryClasses>
      NULL|StandaloneMmPkg/Library/VariableMmDependency/VariableMmDependency.inf
  }
!else
  ArmPkg/Drivers/MmCommunicationDxe/MmCommunication.inf
!endif
