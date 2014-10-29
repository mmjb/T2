

PPBlockInits();
while (i < Pdolen) {
	DName = PPMakeDeviceName();
	if (!DName) { break; }
	status = IoCreateDevice();
	if (STATUS_SUCCESS != status) {
		Pdo[i] = NULL;
		if (STATUS_OBJECT_NAME_COLLISION == status) {
			ExFreePool(DName);
			num++;
			continue;
		}
		break;
	} else {
		i++;
	}
}
num = 0;
PPUnblockInits();