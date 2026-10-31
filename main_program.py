"""A desktop airline booking system using a FIFO booking-request queue."""

from collections import deque
from dataclasses import dataclass
from itertools import count
import json
from pathlib import Path
import tkinter as tk
from tkinter import messagebox, ttk


@dataclass
class Flight:
    """A flight with a fixed number of seats."""

    flight_number: str
    origin: str
    destination: str
    departure_time: str
    capacity: int
    booked_seats: int = 0

    def __post_init__(self) -> None:
        if not self.flight_number.strip():
            raise ValueError("Flight number cannot be empty.")
        if self.capacity <= 0:
            raise ValueError("Flight capacity must be greater than zero.")
        if not 0 <= self.booked_seats <= self.capacity:
            raise ValueError(
                "Booked seats must be within the flight capacity."
            )

    @property
    def available_seats(self) -> int:
        """Return the number of seats that have not been booked."""
        return self.capacity - self.booked_seats

    def reserve_seat(self) -> str:
        """Reserve a seat and return its label."""
        if self.available_seats <= 0:
            raise ValueError(f"Flight {self.flight_number} is fully booked.")

        self.booked_seats += 1
        return f"{self.flight_number}-{self.booked_seats:03d}"


@dataclass(frozen=True)
class Passenger:
    """A passenger who has requested a flight booking."""

    name: str

    def __post_init__(self) -> None:
        if not self.name.strip():
            raise ValueError("Passenger name cannot be empty.")


@dataclass(frozen=True)
class BookingRequest:
    """A passenger's request to book a particular flight."""

    passenger: Passenger
    flight_number: str


@dataclass(frozen=True)
class Booking:
    """A confirmed booking with its assigned seat."""

    booking_id: int
    passenger: Passenger
    flight_number: str
    seat_number: str


class Stack:
    """A stack that follows the Last In, First Out (LIFO) principle."""

    def __init__(self) -> None:
        self._items = []

    def push(self, item: Booking) -> None:
        """Add an item to the top of the stack."""
        self._items.append(item)

    def pop(self) -> Booking | None:
        """Remove and return the most recently added item."""
        if self.is_empty():
            return None
        return self._items.pop()

    def peek(self) -> Booking | None:
        """Return the top item without removing it."""
        if self.is_empty():
            return None
        return self._items[-1]

    def is_empty(self) -> bool:
        """Check whether the stack has no items."""
        return len(self._items) == 0


class AirlineBookingSystem:
    """Manage flights, FIFO booking requests, and confirmed bookings."""

    def __init__(self, flights: list[Flight]) -> None:
        if not flights:
            raise ValueError("At least one flight must be provided.")
        self._flights = {flight.flight_number: flight for flight in flights}
        if len(self._flights) != len(flights):
            raise ValueError("Flight numbers must be unique.")

        self._booking_queue: deque[BookingRequest] = deque()
        self._bookings: list[Booking] = []
        self._booking_stack = Stack()
        self._booking_ids = count(1)
        self.load_from_json()

    @property
    def flights(self) -> tuple[Flight, ...]:
        """Return the available flights."""
        return tuple(self._flights.values())

    @property
    def pending_requests(self) -> tuple[BookingRequest, ...]:
        """Return queued requests in FIFO order."""
        return tuple(self._booking_queue)

    @property
    def bookings(self) -> tuple[Booking, ...]:
        """Return all confirmed bookings."""
        return tuple(self._bookings)

    def save_to_json(self, filepath: str = "bookings.json") -> None:
        """Save confirmed bookings to a JSON file."""
        data = [
            {
                "booking_id": b.booking_id,
                "passenger_name": b.passenger.name,
                "flight_number": b.flight_number,
                "seat_number": b.seat_number,
            }
            for b in self._bookings
        ]
        with open(filepath, "w") as file:
            json.dump(data, file, indent=4)

    def load_from_json(self, filepath: str = "bookings.json") -> None:
        """Load confirmed bookings from a JSON file if it exists."""
        path = Path(filepath)
        if not path.exists():
            return

        with open(filepath, "r") as file:
            data = json.load(file)

        max_id = 0
        for item in data:
            flight = self._flights.get(item["flight_number"])
            if flight and flight.available_seats > 0:
                flight.booked_seats += 1
                booking = Booking(
                    booking_id=item["booking_id"],
                    passenger=Passenger(item["passenger_name"]),
                    flight_number=item["flight_number"],
                    seat_number=item["seat_number"],
                )
                self._bookings.append(booking)
                self._booking_stack.push(booking)
                if item["booking_id"] > max_id:
                    max_id = item["booking_id"]

        self._booking_ids = count(max_id + 1)

    def queue_booking(self, passenger_name: str, flight_number: str) -> None:
        """Add a valid booking request to the end of the FIFO queue."""
        flight_number = flight_number.strip().upper()
        if flight_number not in self._flights:
            raise ValueError(f"Unknown flight number: {flight_number}")

        passenger = Passenger(passenger_name.strip())
        self._booking_queue.append(BookingRequest(passenger, flight_number))

    def process_booking_queue(self) -> list[str]:
        """Process every queued request in arrival order."""
        results = []
        while self._booking_queue:
            request = self._booking_queue.popleft()
            flight = self._flights[request.flight_number]
            if flight.available_seats == 0:
                results.append(
                    f"Could not book {request.passenger.name} on "
                    f"{flight.flight_number}: the flight is fully booked."
                )
                continue
            seat_number = flight.reserve_seat()
            booking = Booking(
                booking_id=next(self._booking_ids),
                passenger=request.passenger,
                flight_number=flight.flight_number,
                seat_number=seat_number,
            )
            self._bookings.append(booking)
            self._booking_stack.push(booking)
            results.append(
                f"Confirmed booking #{booking.booking_id} for "
                f"{booking.passenger.name} on {booking.flight_number}; "
                f"seat {booking.seat_number}."
            )
        self.save_to_json()
        return results

    def undo_last_booking(self) -> Booking | None:
        """Undo the most recently confirmed booking using the stack."""
        booking = self._booking_stack.pop()

        if booking is None:
            return None

        self._bookings.remove(booking)
        flight = self._flights[booking.flight_number]
        flight.booked_seats -= 1

        self.save_to_json()
        return booking


def display_flights(system: AirlineBookingSystem) -> None:
    """Print each flight and its remaining seat count."""
    print("\nAvailable flights")
    print("-" * 72)
    for flight in system.flights:
        print(
            f"{flight.flight_number}: {flight.origin} to {flight.destination} | "
            f"{flight.departure_time} | "
            f"{flight.available_seats}/{flight.capacity} seats available"
        )


def display_pending_requests(system: AirlineBookingSystem) -> None:
    """Print queued requests from first to last."""
    print("\nPending booking requests (FIFO)")
    if not system.pending_requests:
        print("There are no pending requests.")
        return

    for position, request in enumerate(system.pending_requests, start=1):
        print(
            f"{position}. {request.passenger.name} - "
            f"{request.flight_number}"
        )


def display_bookings(system: AirlineBookingSystem) -> None:
    """Print all confirmed bookings."""
    print("\nConfirmed bookings")
    if not system.bookings:
        print("There are no confirmed bookings.")
        return

    for booking in system.bookings:
        print(
            f"#{booking.booking_id}: {booking.passenger.name} - "
            f"{booking.flight_number} - seat {booking.seat_number}"
        )


class AirlineBookingApp:
    """Tkinter interface for the airline booking system."""

    def __init__(self, root: tk.Tk, system: AirlineBookingSystem) -> None:
        self.root = root
        self.system = system
        self.status_text = tk.StringVar(
            value="Select a flight to get started."
        )

        self.root.title("Airline Booking Desk")
        self.root.geometry("1080x760")
        self.root.minsize(850, 620)
        self.root.configure(background="#f3f6fb")

        self._configure_styles()
        self._build_interface()
        self._refresh_tables()

    def _configure_styles(self) -> None:
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("App.TFrame", background="#f3f6fb")
        style.configure("Card.TFrame", background="#ffffff")
        style.configure(
            "Title.TLabel",
            background="#f3f6fb",
            foreground="#102a43",
            font=("Segoe UI", 23, "bold"),
        )
        style.configure(
            "Subtitle.TLabel",
            background="#f3f6fb",
            foreground="#52667a",
            font=("Segoe UI", 10),
        )
        style.configure(
            "Section.TLabel",
            background="#ffffff",
            foreground="#102a43",
            font=("Segoe UI", 12, "bold"),
        )
        style.configure(
            "CardText.TLabel",
            background="#ffffff",
            foreground="#52667a",
            font=("Segoe UI", 9),
        )
        style.configure(
            "Treeview",
            rowheight=29,
            background="#ffffff",
            fieldbackground="#ffffff",
            foreground="#243b53",
            font=("Segoe UI", 9),
        )
        style.configure(
            "Treeview.Heading",
            background="#eaf0f7",
            foreground="#334e68",
            font=("Segoe UI", 9, "bold"),
        )
        style.map(
            "Treeview",
            background=[("selected", "#d9eafd")],
            foreground=[("selected", "#102a43")],
        )
        style.configure(
            "Accent.TButton",
            background="#1769aa",
            foreground="#ffffff",
            font=("Segoe UI", 9, "bold"),
            padding=(12, 8),
        )
        style.map("Accent.TButton", background=[("active", "#0f568f")])
        style.configure("TButton", font=("Segoe UI", 9), padding=(10, 7))

    def _build_interface(self) -> None:
        container = ttk.Frame(self.root, style="App.TFrame", padding=24)
        container.pack(fill="both", expand=True)
        container.columnconfigure(0, weight=1)
        container.rowconfigure(2, weight=3)
        container.rowconfigure(3, weight=2)
        ttk.Label(
            container, text="Airline Booking Desk", style="Title.TLabel"
        ).grid(row=0, column=0, sticky="w")
        flight_card = ttk.Frame(
            container, style="Card.TFrame", padding=16
        )
        flight_card.grid(row=2, column=0, sticky="nsew", pady=(0, 14))
        flight_card.columnconfigure(0, weight=1)
        flight_card.rowconfigure(2, weight=1)
        ttk.Label(
            flight_card, text="Available flights", style="Section.TLabel"
        ).grid(row=0, column=0, sticky="w")
        ttk.Label(
            flight_card,
            text="Choose a flight, enter the passenger name, and add the request to the queue.",
            style="CardText.TLabel",
        ).grid(row=1, column=0, sticky="w", pady=(3, 10))
        self.flight_table = ttk.Treeview(
            flight_card,
            columns=("flight", "route", "departure", "seats"),
            show="headings",
            selectmode="browse",
            height=5,
        )
        for column, title, width in (
            ("flight", "Flight", 110),
            ("route", "Route", 430),
            ("departure", "Departure", 150),
            ("seats", "Seats available", 150),
        ):
            self.flight_table.heading(column, text=title)
            self.flight_table.column(column, width=width, anchor="w")
        self.flight_table.grid(row=2, column=0, sticky="nsew")
        form = ttk.Frame(flight_card, style="Card.TFrame")
        form.grid(row=3, column=0, sticky="ew", pady=(12, 0))
        form.columnconfigure(1, weight=1)
        ttk.Label(form, text="Passenger name", style="CardText.TLabel").grid(
            row=0, column=0, sticky="w", padx=(0, 10)
        )
        self.passenger_name = ttk.Entry(form)
        self.passenger_name.grid(row=0, column=1, sticky="ew", padx=(0, 12))
        self.passenger_name.bind("<Return>", self._queue_booking)
        ttk.Button(
            form,
            text="Add to booking queue",
            style="Accent.TButton",
            command=self._queue_booking,
        ).grid(row=0, column=2)
        lower = ttk.Frame(container, style="App.TFrame")
        lower.grid(row=3, column=0, sticky="nsew")
        lower.columnconfigure(0, weight=1)
        lower.columnconfigure(1, weight=1)
        lower.rowconfigure(0, weight=1)
        queue_card = ttk.Frame(lower, style="Card.TFrame", padding=16)
        queue_card.grid(row=0, column=0, sticky="nsew", padx=(0, 7))
        queue_card.columnconfigure(0, weight=1)
        queue_card.rowconfigure(2, weight=1)
        ttk.Label(
            queue_card, text="Booking queue · FIFO", style="Section.TLabel"
        ).grid(row=0, column=0, sticky="w")
        ttk.Label(
            queue_card,
            text="Requests are confirmed in the order they were added.",
            style="CardText.TLabel",
        ).grid(row=1, column=0, sticky="w", pady=(3, 8))
        self.queue_table = ttk.Treeview(
            queue_card,
            columns=("position", "passenger", "flight"),
            show="headings",
            height=5,
        )
        for column, title, width in (
            ("position", "Queue", 65),
            ("passenger", "Passenger", 190),
            ("flight", "Flight", 100),
        ):
            self.queue_table.heading(column, text=title)
            self.queue_table.column(column, width=width, anchor="w")
        self.queue_table.grid(row=2, column=0, sticky="nsew")
        ttk.Button(
            queue_card,
            text="Process queue",
            style="Accent.TButton",
            command=self._process_queue,
        ).grid(row=3, column=0, sticky="e", pady=(10, 0))
        bookings_card = ttk.Frame(lower, style="Card.TFrame", padding=16)
        bookings_card.grid(row=0, column=1, sticky="nsew", padx=(7, 0))
        bookings_card.columnconfigure(0, weight=1)
        bookings_card.rowconfigure(1, weight=1)
        ttk.Label(
            bookings_card, text="Confirmed bookings", style="Section.TLabel"
        ).grid(row=0, column=0, sticky="w", pady=(0, 8))
        self.booking_table = ttk.Treeview(
            bookings_card,
            columns=("booking", "passenger", "flight", "seat"),
            show="headings",
            height=6,
        )
        for column, title, width in (
            ("booking", "ID", 55),
            ("passenger", "Passenger", 155),
            ("flight", "Flight", 85),
            ("seat", "Seat", 100),
        ):
            self.booking_table.heading(column, text=title)
            self.booking_table.column(column, width=width, anchor="w")
        self.booking_table.grid(row=1, column=0, sticky="nsew")
        ttk.Button(
            bookings_card,
            text="Undo Last Booking",
            command=self._undo_last_booking,
        ).grid(row=2, column=0, sticky="e", pady=(10, 0))
        ttk.Label(
            container, textvariable=self.status_text, style="Subtitle.TLabel"
        ).grid(row=4, column=0, sticky="w", pady=(12, 0))

    def _refresh_tables(self) -> None:
        for table in (self.flight_table, self.queue_table, self.booking_table):
            table.delete(*table.get_children())
        for flight in self.system.flights:
            self.flight_table.insert(
                "",
                "end",
                iid=flight.flight_number,
                values=(
                    flight.flight_number,
                    f"{flight.origin} to {flight.destination}",
                    flight.departure_time,
                    f"{flight.available_seats}/{flight.capacity}",
                ),
            )
        for position, request in enumerate(
            self.system.pending_requests, start=1
        ):
            self.queue_table.insert(
                "",
                "end",
                values=(position, request.passenger.name,
                        request.flight_number),
            )
        for booking in self.system.bookings:
            self.booking_table.insert(
                "",
                "end",
                values=(
                    booking.booking_id,
                    booking.passenger.name,
                    booking.flight_number,
                    booking.seat_number,
                ),
            )

    def _queue_booking(self, _event: tk.Event | None = None) -> None:
        selection = self.flight_table.selection()
        if not selection:
            messagebox.showwarning(
                "Select a flight",
                "Choose a flight before adding a booking request.",
                parent=self.root,
            )
            return
        try:
            self.system.queue_booking(
                self.passenger_name.get(), selection[0]
            )
        except ValueError as error:
            messagebox.showerror(
                "Unable to add request", str(error), parent=self.root
            )
            return

        self.passenger_name.delete(0, "end")
        self._refresh_tables()
        self.status_text.set(
            "Booking request added to the end of the FIFO queue.")

    def _process_queue(self) -> None:
        results = self.system.process_booking_queue()
        self._refresh_tables()
        if not results:
            self.status_text.set("There are no booking requests to process.")
            return

        self.status_text.set(
            f"Processed {len(results)} booking request(s) in FIFO order."
        )
        messagebox.showinfo(
            "Booking queue processed",
            "\n".join(results),
            parent=self.root,
        )

    def _undo_last_booking(self) -> None:
        booking = self.system.undo_last_booking()
        if booking is None:
            self.status_text.set("There are no confirmed bookings to undo.")
            messagebox.showinfo(
                "Nothing to undo",
                "There are no confirmed bookings to undo.",
                parent=self.root,
            )
            return

        self._refresh_tables()
        self.status_text.set(
            f"Undid booking #{booking.booking_id} for "
            f"{booking.passenger.name}."
        )
        messagebox.showinfo(
            "Booking undone",
            f"Booking #{booking.booking_id} for "
            f"{booking.passenger.name} has been undone.",
            parent=self.root,
        )


def create_booking_system() -> AirlineBookingSystem:
    """Create the sample flights used by the application."""
    return AirlineBookingSystem(
        [
            Flight("PH101", "Manila", "Cebu", "08:30", 120),
            Flight("PH205", "Cebu", "Davao", "11:15", 100),
            Flight("PH310", "Manila", "Puerto Princesa", "14:00", 80),
        ]
    )


def main() -> None:
    """Launch the desktop airline booking interface."""
    root = tk.Tk()
    AirlineBookingApp(root, create_booking_system())
    root.mainloop()


if __name__ == "__main__":
    main()