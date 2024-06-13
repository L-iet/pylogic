import json
import sys
import os
import datetime as dt
from typing import Literal, TypedDict
from enum import Enum

SEEK_END = 2
MessageDict = TypedDict("MessageDict", {"time": str, "msg": str})
SessionDict = TypedDict(
    "SessionDict",
    {
        "start_time": str,
        "end_time": str,
        "start_message": str,
        "end_message": str,
        "messages": list[MessageDict],
    },
)


class Action(Enum):
    LOGOUT = 1
    NEW_MESSAGE = 2
    NEW_MESSAGE_DONE = 3
    NEW_MESSAGE_ABORT = 4
    RENDER_NEW_MESSAGE = 5
    RENDER_MESSAGES = 6
    RENDER_MESSAGE = 7
    SAVE_TO_MD = 8
    HELP = 9
    UNKNOWN = 10


class Actions:
    """
    Holds all posible actions.
    """

    def __init__(self) -> None:
        self.logged_in: bool = True
        self.editing_new_message: bool = False


class Message:
    def __init__(self, msg_time: dt.datetime, msg: str) -> None:
        self.time: dt.datetime = msg_time
        self.msg: str = msg

    def as_dict(self) -> MessageDict:
        return {"time": self.time.isoformat(), "msg": self.msg}

    def as_json(self, indent: int | None = None) -> str:
        return json.dumps(self.as_dict(), indent=indent)


class Session:
    def __init__(self, start_time: dt.datetime, start_message: str | None = None):
        self.start_time: dt.datetime = start_time
        self.end_time: dt.datetime | None = None
        self.start_message_str: str = (
            "Begin session."
            if start_message is None
            else f"Begin session.\n{start_message}"
        )
        self.start_message: Message = Message(start_time, self.start_message_str)
        self.end_message_str: str = "End session."
        self.messages: list[Message] = [
            self.start_message
        ]  # messages during the session
        self.actions: Actions = Actions()

    @property
    def ended(self) -> bool:
        return self.end_time is not None

    def add_message(self, msg: str, time: dt.datetime | None = None) -> None:
        assert not self.ended, "Session has ended."
        self.messages.append(Message(time or dt.datetime.now().astimezone(), msg))

    def _render_messages(self) -> str | None:
        if not self.messages:
            print("No messages.")
            return
        md = "\n\n".join(
            [m.time.strftime("%H:%M:%S") + "\n" + m.msg for m in self.messages[1:]]
        )
        md = (
            "# "
            + self.start_time.strftime("%Y-%m-%d %H:%M:%S")
            + "\n"
            + self.start_message_str
            + "\n\n"
            + md
        )
        return md

    def render_messages(self) -> None:
        md = self._render_messages()
        if md is None:
            return
        with open("_session_temp.md", "w") as f:
            f.write(md)
        render_temp_file()
        clear_temp_file()

    def save_to_md(self, filename: str) -> None:
        md = self._render_messages()
        if md is None:
            return
        if not filename.endswith(".md"):
            filename += ".md"
        with open(filename, "w") as f:
            f.write(md)
        print(f"Messages saved to {filename}.")

    def render_message(self, index: int) -> None:
        if not self.messages:
            print("No messages.")
            return
        try:
            m = self.messages[index]
        except IndexError:
            print("Invalid index. Available indices: 0 to", len(self.messages) - 1)
            return
        md = m.time.strftime("%H:%M:%S") + "\n" + m.msg
        with open("_session_temp.md", "w") as f:
            f.write(md)
        render_temp_file()
        clear_temp_file()

    def as_dict(self) -> SessionDict:
        return {
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat() if self.ended else None,  # type: ignore
            "start_message": self.start_message_str,
            "end_message": self.end_message_str if self.ended else None,
            "messages": [m.as_dict() for m in self.messages],
        }

    def as_json(self, indent: int | None = None) -> str:
        return json.dumps(self.as_dict(), indent=indent)


def add_session_to_db(session: Session):
    assert session.ended, "Session must be ended before adding to database."
    with open("_session.json", "r+") as f:
        f.seek(0, SEEK_END)
        end = f.tell()
        f.seek(end - 2)
        f.write("," + session.as_json() + "\n]}")


def login() -> Session:
    now = dt.datetime.now().astimezone()
    if len(sys.argv) > 1:
        s = Session(now, sys.argv[1])
    else:
        s = Session(now)
    return s


def get_logout_message_and_confirmation(cmds: list[str]) -> tuple[str | None, bool]:
    msg = None
    confirmed = False
    try:
        dash_m = cmds.index("-m")
        msg = ""
        for i in range(dash_m + 1, len(cmds)):
            if cmds[i].startswith("-"):
                break
            msg += cmds[i] + " "
        msg = msg.rstrip()
    except (ValueError, IndexError):
        msg = input("End message: ") or None
    try:
        cmds.index("-y")
        confirmed = True
    except ValueError:
        confirmed = input("End session? (y/n): ").strip().lower() == "y"
    return msg, confirmed


def try_logout(s: Session, msg: str | None = None, confirmed: bool = False) -> bool:
    if s.actions.editing_new_message:
        print("Finish editing new message first.")
        print("Type 'done' or 'nmd' to finish editing.")
        return False
    if s.ended:
        print("Session has already ended.")
        return False
    if not confirmed:
        print("Session not ended.")
        return False
    if msg is not None:
        end_time = dt.datetime.now().astimezone()
        s.end_message_str = f"End session.\n{msg}"
        s.add_message(s.end_message_str, end_time)
        s.end_time = end_time
    add_session_to_db(s)
    s.actions.logged_in = False
    print("Session ended.")
    return True


PWSH = r'C:\"Program Files"\WindowsApps\Microsoft.PowerShell_7.4.2.0_x64__8wekyb3d8bbwe\pwsh.exe'


def render_temp_file() -> None:
    os.system(f'{PWSH} -command "Show-Markdown -Path _session_temp.md"')


def clear_temp_file() -> None:
    open("_session_temp.md", "w").close()


def try_add_new_message(s: Session) -> bool:
    if s.actions.editing_new_message:
        return False
    s.actions.editing_new_message = True
    print("Type message in _session_temp.md and save.")
    os.system("subl _session_temp.md")
    return True


def try_render_new_message(s: Session) -> bool:
    if not s.actions.editing_new_message:
        return False
    print("***Rendering new message...***")
    render_temp_file()
    return True


def try_render_messages(s: Session) -> bool:
    if s.actions.editing_new_message:
        print("Finish editing new message first.")
        print("Type 'done' or 'nmd' to finish editing.")
        return False
    s.render_messages()
    return True


def get_filename_save_to_md(cmds: list[str]) -> str:
    if len(cmds) > 1:
        filename = cmds[1]
    else:
        filename = input("Filename: ")
        now = dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
        filename = filename or f"pylogic_session_{now}.md"
    return filename


def try_save_to_md(s: Session, filename: str) -> bool:
    if s.actions.editing_new_message:
        print("Finish editing new message first.")
        print("Type 'done' or 'nmd' to finish editing.")
        return False
    s.save_to_md(filename)
    return True


def try_new_message_done(s: Session) -> bool:
    if not s.actions.editing_new_message:
        return False
    s.actions.editing_new_message = False
    with open("_session_temp.md", "r") as f:
        msg = f.read()
        s.add_message(msg)
    clear_temp_file()
    print("Message added; Temp file cleared.")
    return True


def try_new_message_abort(s: Session) -> bool:
    if not s.actions.editing_new_message:
        return False
    s.actions.editing_new_message = False
    clear_temp_file()
    print("Message aborted; Temp file cleared.")
    return True


commands = {
    "nm": Action.NEW_MESSAGE,
    "nmd": Action.NEW_MESSAGE_DONE,
    "nma": Action.NEW_MESSAGE_ABORT,
    "abort": Action.NEW_MESSAGE_ABORT,
    "smd": Action.SAVE_TO_MD,
    "help": Action.HELP,
    "logout": Action.LOGOUT,
    "lo": Action.LOGOUT,
    "exit": Action.LOGOUT,
    "quit": Action.LOGOUT,
    "q": Action.LOGOUT,
    # "render": Action.RENDER_NEW_MESSAGE,
}


def print_help() -> Literal[True]:
    print("Commands:")
    print(
        " ".join(commands.keys()),
        "render/r",
        "abort",
        "done/save",
        "save <filename>",
    )
    return True


def main():
    session = login()
    print("Session started.")
    while True:
        print_help()
        cmds = input("|> ").strip().split()
        if not cmds:
            continue
        cmd = cmds[0]
        act = commands.get(cmd, Action.UNKNOWN)
        if act == Action.NEW_MESSAGE:
            try_add_new_message(session)
        elif act == Action.NEW_MESSAGE_DONE:
            try_new_message_done(session)
        elif act == Action.NEW_MESSAGE_ABORT:
            try_new_message_abort(session)
        elif act == Action.SAVE_TO_MD:
            filename = get_filename_save_to_md(cmds)
            try_save_to_md(session, filename)
        elif act == Action.HELP:
            print_help()
        elif act == Action.LOGOUT:
            if try_logout(session, *get_logout_message_and_confirmation(cmds)):
                break
        elif cmd in ["save", "done"]:
            _ = try_new_message_done(session) or try_save_to_md(
                session, get_filename_save_to_md(cmds)
            )
        elif cmd in ["r", "render"]:
            _ = try_render_new_message(session) or try_render_messages(session)


if __name__ == "__main__":
    main()
