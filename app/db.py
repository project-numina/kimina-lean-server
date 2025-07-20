from app.prisma_client import prisma


class DataLayer:
    def __init__(self) -> None:
        self.client = prisma
        self.connected = False

    async def connect(self) -> None:
        try:
            await self.client.connect()
            self.connected = True
        except:
            self.connected = False

    async def disconnect(self) -> None:
        if self.connected:
            await self.client.disconnect()
            self.connected = False


db = DataLayer()
